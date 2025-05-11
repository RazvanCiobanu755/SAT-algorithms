import time
from collections import defaultdict, deque

class CDCLSolver:
    def __init__(self):
        self.clauses = []
        self.variables = set()
        self.assignment = {}
        self.decision_level = 0
        self.var_info = {}  # Stores decision level and antecedent clause for each variable
        self.watch_list = defaultdict(list)
        self.occurrences = defaultdict(int)
        self.learned_clauses = []
        self.trail = []
        self.trail_lim = []
        self.conflict_count = 0
        self.restart_threshold = 100
        self.var_activity = defaultdict(float)
        self.var_order = []

    def parse_dimacs(self, dimacs_str):
        lines = dimacs_str.split('\n')
        for line in lines:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('p'):
                continue
            clause = []
            for lit in line.split()[:-1]:  # Skip the 0 at end
                lit = int(lit)
                if lit == 0:
                    continue
                var = abs(lit)
                self.variables.add(var)
                clause.append(lit)
            if clause:
                self.clauses.append(tuple(clause))
        self.initialize_data_structures()

    def initialize_data_structures(self):
        # Initialize watch lists and activity scores
        for var in self.variables:
            self.var_activity[var] = 0.0
            self.var_order.append(var)
        
        # Initialize watch lists with two watched literals per clause
        for clause_idx, clause in enumerate(self.clauses):
            if len(clause) > 0:
                first_lit = clause[0]
                self.watch_list[first_lit].append(clause_idx)
                if len(clause) > 1:
                    second_lit = clause[1]
                    self.watch_list[second_lit].append(clause_idx)

    def solve(self):
        start_time = time.time()
        result = self.cdcl()
        elapsed = time.time() - start_time
        return result, elapsed

    def cdcl(self):
        while True:
            # Unit propagation
            conflict_clause = self.unit_propagation()
            if conflict_clause is not None:
                self.conflict_count += 1
                
                # Check for top-level conflict
                if self.decision_level == 0:
                    return False
                
                # Learn conflict clause and backtrack
                learned_clause, backtrack_level = self.analyze_conflict(conflict_clause)
                self.learned_clauses.append(learned_clause)
                self.add_clause(learned_clause)
                self.backtrack(backtrack_level)
                
                # Bump variable activities
                self.bump_activity(learned_clause)
                
                # Restart if needed
                if self.conflict_count >= self.restart_threshold:
                    self.restart_threshold *= 1.5
                    self.backtrack(0)
            else:
                # Check if all variables are assigned
                if all(var in self.assignment for var in self.variables):
                    return True
                
                # Decision - select unassigned variable
                var = self.select_variable()
                if var is None:
                    return True  # All variables assigned
                
                self.decision_level += 1
                self.trail_lim.append(len(self.trail))
                
                # Try assigning True first (or use polarity heuristic)
                value = True
                self.assign(var, value, None)

    def unit_propagation(self):
        while len(self.trail) < len(self.assignment):
            # Get next unprocessed assignment
            lit = next(lit for lit in self.assignment if abs(lit) not in {abs(x) for x in self.trail})
            var = abs(lit)
            value = lit > 0
            
            # Process all clauses watching the negation of this literal
            neg_lit = -lit
            to_remove = []
            for clause_idx in self.watch_list.get(neg_lit, []):
                clause = self.clauses[clause_idx] if clause_idx < len(self.clauses) else self.learned_clauses[clause_idx - len(self.clauses)]
                
                # Find a new literal to watch
                new_watch = None
                for other_lit in clause:
                    other_var = abs(other_lit)
                    if other_lit != neg_lit and other_var not in self.assignment:
                        new_watch = other_lit
                        break
                    elif other_var in self.assignment and self.assignment[other_var] == (other_lit > 0):
                        new_watch = other_lit  # Clause is already satisfied
                        break
                
                if new_watch is not None:
                    # Update watch list
                    self.watch_list[new_watch].append(clause_idx)
                    to_remove.append((neg_lit, clause_idx))
                else:
                    # Clause is unit or conflicting
                    unassigned = []
                    satisfied = False
                    for l in clause:
                        v = abs(l)
                        if v not in self.assignment:
                            unassigned.append(l)
                        elif self.assignment[v] == (l > 0):
                            satisfied = True
                            break
                    
                    if satisfied:
                        continue
                    elif len(unassigned) == 1:
                        # Unit clause found
                        unit_lit = unassigned[0]
                        unit_var = abs(unit_lit)
                        if unit_var in self.assignment:
                            if self.assignment[unit_var] != (unit_lit > 0):
                                return clause  # Conflict
                        else:
                            self.assign(unit_var, unit_lit > 0, clause_idx)
                    else:
                        # Conflict found
                        return clause
        
            # Remove processed watches
            for lit, idx in to_remove:
                if idx in self.watch_list.get(lit, []):
                    self.watch_list[lit].remove(idx)
        
        return None

    def assign(self, var, value, antecedent):
        lit = var if value else -var
        self.assignment[lit] = True
        self.var_info[var] = (self.decision_level, antecedent)
        self.trail.append(lit)

    def analyze_conflict(self, conflict_clause):
        # Implement conflict analysis (1st UIP learning)
        learned_clause = []
        backtrack_level = 0
        seen = set()
        current_level_lits = []
        
        # Start with the conflict clause
        queue = deque()
        for lit in conflict_clause:
            var = abs(lit)
            queue.append(var)
            seen.add(var)
        
        while queue:
            var = queue.popleft()
            level, antecedent = self.var_info.get(var, (0, None))
            
            if level == self.decision_level:
                current_level_lits.append(var)
            if antecedent is None:
                continue  # Decision variable
            
            # Resolve with antecedent clause
            antecedent_clause = self.clauses[antecedent] if antecedent < len(self.clauses) else self.learned_clauses[antecedent - len(self.clauses)]
            for lit in antecedent_clause:
                v = abs(lit)
                if v != var and v not in seen:
                    seen.add(v)
                    queue.append(v)
        
        # Find the 1st UIP
        if current_level_lits:
            uip = current_level_lits[-1]  # Simplified - should implement proper UIP detection
            learned_clause = [lit for lit in conflict_clause if abs(lit) != uip]
            
            # Compute backtrack level
            if len(current_level_lits) > 1:
                backtrack_level = max(self.var_info[v][0] for v in current_level_lits if v != uip)
            else:
                backtrack_level = 0
        
        return tuple(learned_clause), backtrack_level

    def backtrack(self, level):
        # Undo assignments above the backtrack level
        while self.decision_level > level:
            self.decision_level -= 1
            lim = self.trail_lim.pop()
            while len(self.trail) > lim:
                lit = self.trail.pop()
                var = abs(lit)
                del self.assignment[lit]
                if var in self.var_info:
                    del self.var_info[var]

    def select_variable(self):
        # VSIDS heuristic - select variable with highest activity
        unassigned = [var for var in self.var_order if var not in self.assignment]
        if not unassigned:
            return None
        
        # Sort by activity (descending)
        unassigned.sort(key=lambda v: -self.var_activity[v])
        return unassigned[0]

    def bump_activity(self, clause):
        # Increase activity of variables in the learned clause
        for lit in clause:
            var = abs(lit)
            self.var_activity[var] += 1.0
        
        # Decay all activities periodically
        if self.conflict_count % 100 == 0:
            for var in self.var_activity:
                self.var_activity[var] *= 0.95

    def add_clause(self, clause):
        # Add a learned clause to the solver
        self.learned_clauses.append(clause)
        if len(clause) > 0:
            first_lit = clause[0]
            self.watch_list[first_lit].append(len(self.clauses) + len(self.learned_clauses) - 1)
            if len(clause) > 1:
                second_lit = clause[1]
                self.watch_list[second_lit].append(len(self.clauses) + len(self.learned_clauses) - 1)

def get_dimacs_input():
    print("Enter DIMACS format clauses (type 'done' when finished):")
    input_lines = []
    while True:
        line = input().strip()
        if line.lower() == 'done':
            break
        input_lines.append(line)
    return '\n'.join(input_lines)

if __name__ == "__main__":
    solver = CDCLSolver()
    dimacs_input = get_dimacs_input()
    solver.parse_dimacs(dimacs_input)
    
    result, elapsed = solver.solve()
    
    print("\nThe formula is", "satisfiable" if result else "unsatisfiable")
    print(f"Solving time: {elapsed:.4f} seconds")
