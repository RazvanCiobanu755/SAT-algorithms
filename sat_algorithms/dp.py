import time
from collections import defaultdict

class Solver:
    def __init__(self):
        self.clauses = []
        self.variables = set()
        self.assignment = {}
        self.pure_lits = set()

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
                self.clauses.append(tuple(clause))  # Store as tuple for hashability

    def solve(self):
        start_time = time.time()
        
        while True:
            # 1. Unit propagation
            changed = True
            while changed:
                changed = self.unit_propagation()
                if self.contradiction_found():
                    elapsed = time.time() - start_time
                    return False, elapsed
            
            # 2. Pure literal elimination
            self.find_pure_literals()
            if self.pure_lits:
                self.apply_pure_literals()
                continue
            
            # 3. Variable elimination
            if not self.variables:
                elapsed = time.time() - start_time
                return True, elapsed
                
            var = self.select_variable()
            self.apply_variable_elimination(var)
    
    def unit_propagation(self):
        changed = False
        new_clauses = []
        
        # First pass to find unit clauses
        unit_clauses = [c[0] for c in self.clauses if len(c) == 1]
        
        for lit in unit_clauses:
            var = abs(lit)
            if var in self.assignment:
                if (lit > 0 and not self.assignment[var]) or (lit < 0 and self.assignment[var]):
                    continue  # Contradiction will be caught later
            else:
                self.assignment[var] = lit > 0
                changed = True
        
        if not changed:
            return False
            
        # Filter satisfied clauses and simplify others
        for clause in self.clauses:
            new_clause = []
            satisfied = False
            for lit in clause:
                var = abs(lit)
                if var in self.assignment:
                    if (lit > 0 and self.assignment[var]) or (lit < 0 and not self.assignment[var]):
                        satisfied = True
                        break
                else:
                    new_clause.append(lit)
            
            if not satisfied:
                new_clauses.append(tuple(new_clause))  # Store as tuple
        
        self.clauses = new_clauses
        return True
    
    def find_pure_literals(self):
        lit_counts = defaultdict(int)
        self.pure_lits = set()
        
        for clause in self.clauses:
            for lit in clause:
                lit_counts[lit] += 1
        
        for lit in lit_counts:
            if -lit not in lit_counts:
                self.pure_lits.add(lit)
    
    def apply_pure_literals(self):
        new_clauses = []
        pure_vars = set(abs(lit) for lit in self.pure_lits)
        
        for lit in self.pure_lits:
            var = abs(lit)
            self.assignment[var] = lit > 0
            self.variables.discard(var)
        
        for clause in self.clauses:
            keep = True
            for lit in clause:
                var = abs(lit)
                if var in pure_vars:
                    keep = False
                    break
            if keep:
                new_clauses.append(clause)
        
        self.clauses = new_clauses
        self.pure_lits = set()
    
    def select_variable(self):
        return next(iter(self.variables))
    
    def apply_variable_elimination(self, var):
        # Resolve all clauses containing var with clauses containing -var
        pos_clauses = [c for c in self.clauses if var in c]
        neg_clauses = [c for c in self.clauses if -var in c]
        
        new_clauses = []
        resolved = set()
        
        # Generate resolvents
        for pc in pos_clauses:
            for nc in neg_clauses:
                resolvent = []
                seen = set()
                for lit in pc:
                    if abs(lit) != var and lit not in seen:
                        resolvent.append(lit)
                        seen.add(lit)
                for lit in nc:
                    if abs(lit) != var and lit not in seen:
                        resolvent.append(lit)
                        seen.add(lit)
                
                # Convert to tuple for hashability
                resolvent_tuple = tuple(sorted(resolvent))
                if resolvent_tuple not in resolved:
                    resolved.add(resolvent_tuple)
                    new_clauses.append(resolvent_tuple)
        
        # Add clauses not containing the variable
        for clause in self.clauses:
            if var not in clause and -var not in clause:
                new_clauses.append(clause)
        
        self.clauses = new_clauses
        self.variables.remove(var)
    
    def contradiction_found(self):
        for clause in self.clauses:
            if not clause:
                return True
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
    solver = Solver()
    dimacs_input = get_dimacs_input()
    solver.parse_dimacs(dimacs_input)
    
    result, elapsed = solver.solve()
    
    print("\nThe formula is", "satisfiable" if result else "unsatisfiable")
    print(f"Solving time: {elapsed:.4f} seconds")
