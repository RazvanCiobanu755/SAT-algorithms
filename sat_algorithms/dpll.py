import time
from collections import defaultdict

class DPLLSolver:
    def __init__(self):
        self.clauses = []
        self.variables = set()
        self.assignment = {}
        self.unit_clauses = set()
        self.watch_list = defaultdict(list)
        self.occurrences = defaultdict(int)

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
                if len(clause) == 1:
                    self.unit_clauses.add(clause[0])

    def solve(self):
        start_time = time.time()
        
        # Initialize watch list
        for i, clause in enumerate(self.clauses):
            if len(clause) > 0:
                first_lit = clause[0]
                self.watch_list[first_lit].append(i)
                if len(clause) > 1:
                    second_lit = clause[1]
                    self.watch_list[second_lit].append(i)
        
        # Count literal occurrences
        for clause in self.clauses:
            for lit in clause:
                self.occurrences[lit] += 1
        
        result = self.dpll()
        elapsed = time.time() - start_time
        return result, elapsed
    
    def dpll(self):
        # Unit propagation
        while self.unit_clauses:
            lit = self.unit_clauses.pop()
            var = abs(lit)
            value = lit > 0
            
            if var in self.assignment:
                if self.assignment[var] != value:
                    return False  # Contradiction
                continue
            
            self.assignment[var] = value
            
            # Process all clauses watching this literal
            to_remove = []
            for clause_idx in self.watch_list.get(lit, []):
                clause = self.clauses[clause_idx]
                new_watch = None
                for other_lit in clause:
                    if other_lit != lit:
                        other_var = abs(other_lit)
                        if other_var not in self.assignment or \
                           (self.assignment[other_var] == (other_lit > 0)):
                            new_watch = other_lit
                            break
                
                if new_watch is None:
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
                        self.unit_clauses.add(unassigned[0])
                    elif not unassigned:
                        return False  # Conflict
            
            # Remove from watch list
            if lit in self.watch_list:
                del self.watch_list[lit]
            if -lit in self.watch_list:
                del self.watch_list[-lit]
        
        # Pure literal elimination
        pure_lits = set()
        for lit in self.occurrences:
            if -lit not in self.occurrences:
                pure_lits.add(lit)
        
        for lit in pure_lits:
            var = abs(lit)
            if var not in self.assignment:
                self.assignment[var] = (lit > 0)
        
        # Check if all clauses are satisfied
        all_satisfied = True
        for clause in self.clauses:
            satisfied = False
            for lit in clause:
                var = abs(lit)
                if var in self.assignment and self.assignment[var] == (lit > 0):
                    satisfied = True
                    break
            if not satisfied:
                all_satisfied = False
                break
        
        if all_satisfied:
            return True
        
        # Select unassigned variable
        unassigned = [var for var in self.variables if var not in self.assignment]
        if not unassigned:
            return True
        
        var = unassigned[0]
        
        # Try assigning True
        self.assignment[var] = True
        result = self.dpll()
        if result:
            return True
        
        # Backtrack and try False
        del self.assignment[var]
        self.assignment[var] = False
        result = self.dpll()
        if result:
            return True
        
        # Undo assignment if both failed
        del self.assignment[var]
        return False

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
    solver = DPLLSolver()
    dimacs_input = get_dimacs_input()
    solver.parse_dimacs(dimacs_input)
    
    result, elapsed = solver.solve()
    
    print("\nThe formula is", "satisfiable" if result else "unsatisfiable")
    print(f"Solving time: {elapsed:.4f} seconds")
