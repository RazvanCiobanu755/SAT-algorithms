import time
from itertools import combinations

class CDCL:
    def __init__(self):
        self.clauses = set()
        self.variables = set()
        self.assignments = {}  # {var: (value, decision_level, antecedent_clause)}
        self.decision_level = 0
        self.decision_steps = 0
        self.unit_propagations = 0
        self.learned_clauses = set()
        self.variable_order = []  # For VSIDS heuristic
        self.variable_activity = {}  # For VSIDS heuristic

    def add_clause(self, clause):
        """Add a clause to the knowledge base"""
        self.clauses.add(frozenset(clause))
        for literal in clause:
            var = abs(literal)
            self.variables.add(var)
            if var not in self.variable_activity:
                self.variable_activity[var] = 0

    def bump_variable_activity(self, var):
        """Increase activity for a variable (VSIDS heuristic)"""
        self.variable_activity[var] += 1

    def decay_variable_activities(self):
        """Decay all variable activities (VSIDS heuristic)"""
        for var in self.variable_activity:
            self.variable_activity[var] *= 0.95

    def unit_propagate(self):
        """Perform unit propagation until no more unit clauses exist"""
        changed = True
        while changed:
            changed = False
            unit_clauses = [c for c in self.clauses.union(self.learned_clauses) if len(c) == 1]
            
            for clause in unit_clauses:
                self.unit_propagations += 1
                literal = next(iter(clause))
                var = abs(literal)
                value = literal > 0
                
                # Skip if already assigned
                if var in self.assignments:
                    if self.assignments[var][0] != value:
                        # Conflict detected
                        return (False, clause)
                    continue
                
                # Add the assignment with current decision level and antecedent clause
                self.assignments[var] = (value, self.decision_level, clause)
                
                # Bump activity for variables in the clause
                for lit in clause:
                    self.bump_variable_activity(abs(lit))
                
                # Remove all clauses containing this literal (they're satisfied)
                self.clauses = {c for c in self.clauses if literal not in c}
                self.learned_clauses = {c for c in self.learned_clauses if literal not in c}
                
                # Remove negations of this literal from all clauses
                new_clauses = set()
                for c in self.clauses:
                    if -literal in c:
                        new_clause = c - {-literal}
                        if not new_clause:  # Empty clause found - conflict
                            return (False, c)
                        new_clauses.add(new_clause)
                    else:
                        new_clauses.add(c)
                self.clauses = new_clauses
                
                new_learned = set()
                for c in self.learned_clauses:
                    if -literal in c:
                        new_clause = c - {-literal}
                        if not new_clause:  # Empty clause found - conflict
                            return (False, c)
                        new_learned.add(new_clause)
                    else:
                        new_learned.add(c)
                self.learned_clauses = new_learned
                
                changed = True
        
        return (True, None)

    def analyze_conflict(self, conflict_clause):
        """Analyze the conflict and learn a new clause"""
        if self.decision_level == 0:
            return None  # Top-level conflict
        
        # Get all variables in the conflict clause that were assigned at current decision level
        current_level_vars = []
        for literal in conflict_clause:
            var = abs(literal)
            if var in self.assignments and self.assignments[var][1] == self.decision_level:
                current_level_vars.append(var)
        
        # If only one variable at current level, we can backtrack further
        while len(current_level_vars) == 1:
            var = current_level_vars[0]
            antecedent = self.assignments[var][2]
            if antecedent is None:  # Decision variable
                break
            
            # Resolve the conflict clause with the antecedent
            new_conflict = (conflict_clause - {-var}).union(antecedent - {var})
            conflict_clause = new_conflict
            
            # Find new current level variables
            current_level_vars = []
            for literal in conflict_clause:
                var = abs(literal)
                if var in self.assignments and self.assignments[var][1] == self.decision_level:
                    current_level_vars.append(var)
        
        # Create the learned clause
        learned_clause = frozenset(conflict_clause)
        self.learned_clauses.add(learned_clause)
        
        # Find the backtrack level (second highest decision level in the learned clause)
        decision_levels = []
        for literal in learned_clause:
            var = abs(literal)
            if var in self.assignments:
                decision_levels.append(self.assignments[var][1])
        
        if len(decision_levels) > 1:
            decision_levels.sort(reverse=True)
            backtrack_level = decision_levels[1]
        else:
            backtrack_level = 0
        
        return (learned_clause, backtrack_level)

    def choose_literal(self):
        """Select an unassigned variable using VSIDS heuristic"""
        unassigned = [var for var in self.variables if var not in self.assignments]
        if not unassigned:
            return None
        
        # Sort by activity (VSIDS heuristic)
        unassigned.sort(key=lambda var: -self.variable_activity.get(var, 0))
        return unassigned[0]

    def solve(self):
        """Execute the CDCL algorithm"""
        # Initial unit propagation
        result, conflict_clause = self.unit_propagate()
        if not result:
            return False
        
        # If all clauses are satisfied, we're done
        if not self.clauses and not any(len(c) > 0 for c in self.learned_clauses):
            return True
        
        while True:
            # Choose a literal to branch on
            var = self.choose_literal()
            if var is None:
                return True  # All variables assigned
            
            self.decision_steps += 1
            self.decision_level += 1
            
            # Try assigning the literal to True first
            self.assignments[var] = (True, self.decision_level, None)
            
            while True:
                result, conflict_clause = self.unit_propagate()
                if result:
                    break  # No conflict
                
                # Analyze conflict and learn clause
                analysis_result = self.analyze_conflict(conflict_clause)
                if analysis_result is None:
                    return False  # Unsatisfiable
                
                learned_clause, backtrack_level = analysis_result
                
                # Backtrack to the appropriate level
                self.backtrack(backtrack_level)
                self.decision_level = backtrack_level
                
                if self.decision_level == 0:
                    # We've backtracked all the way to the top
                    self.learned_clauses.add(learned_clause)
                
                # Add the learned clause and propagate
                self.clauses.add(learned_clause)
                self.decay_variable_activities()
                
                # The learned clause should now be unit, forcing the next assignment
                result, _ = self.unit_propagate()
                if not result:
                    continue  # Another conflict, repeat analysis
            
            # If we get here, the current assignments are consistent
            # Continue with next decision if needed

    def backtrack(self, backtrack_level):
        """Backtrack to the specified decision level"""
        to_remove = []
        for var, (value, level, _) in self.assignments.items():
            if level > backtrack_level:
                to_remove.append(var)
        
        for var in to_remove:
            del self.assignments[var]

    def get_stats(self):
        return {
            "decision_steps": self.decision_steps,
            "unit_propagations": self.unit_propagations,
            "clauses": len(self.clauses),
            "learned_clauses": len(self.learned_clauses),
            "assignments": len(self.assignments)
        }

def encode_sudoku(sudoku_grid):
    """Encode a Sudoku puzzle as propositional clauses for CDCL"""
    n = len(sudoku_grid)
    sqrt_n = int(n ** 0.5)
    cdcl = CDCL()
    
    # Each cell contains at least one number (1..n)
    for row in range(n):
        for col in range(n):
            clause = [row * n * n + col * n + num + 1 for num in range(n)]
            cdcl.add_clause(clause)
    
    # Each cell contains at most one number
    for row in range(n):
        for col in range(n):
            for num1, num2 in combinations(range(n), 2):
                cdcl.add_clause([-(row * n * n + col * n + num1 + 1), 
                               -(row * n * n + col * n + num2 + 1)])
    
    # Each number appears at most once in each row
    for row in range(n):
        for num in range(n):
            for col1, col2 in combinations(range(n), 2):
                cdcl.add_clause([-(row * n * n + col1 * n + num + 1), 
                               -(row * n * n + col2 * n + num + 1)])
    
    # Each number appears at most once in each column
    for col in range(n):
        for num in range(n):
            for row1, row2 in combinations(range(n), 2):
                cdcl.add_clause([-(row1 * n * n + col * n + num + 1), 
                                -(row2 * n * n + col * n + num + 1)])
    
    # Each number appears at most once in each subgrid
    for subgrid_row in range(sqrt_n):
        for subgrid_col in range(sqrt_n):
            for num in range(n):
                cells = []
                for i in range(sqrt_n):
                    for j in range(sqrt_n):
                        row = subgrid_row * sqrt_n + i
                        col = subgrid_col * sqrt_n + j
                        cells.append((row, col))
                
                for (r1, c1), (r2, c2) in combinations(cells, 2):
                    cdcl.add_clause([-(r1 * n * n + c1 * n + num + 1), 
                                    -(r2 * n * n + c2 * n + num + 1)])
    
    # Add pre-filled cells as unit clauses
    for row in range(n):
        for col in range(n):
            if sudoku_grid[row][col] != 0:
                num = sudoku_grid[row][col] - 1
                cdcl.add_clause([row * n * n + col * n + num + 1])
    
    return cdcl

def solve_sudoku_cdcl(sudoku_grid):
    """Solve a Sudoku puzzle using the CDCL algorithm"""
    cdcl = encode_sudoku(sudoku_grid)
    start_time = time.time()
    result = cdcl.solve()
    end_time = time.time()
    
    stats = cdcl.get_stats()
    stats['time'] = end_time - start_time
    
    if result:
        # Reconstruct the solution from the assignments
        n = len(sudoku_grid)
        solution = [[0 for _ in range(n)] for _ in range(n)]
        for var, (value, _, _) in cdcl.assignments.items():
            if value:  # Only consider true assignments
                var_idx = var - 1
                num = var_idx % n + 1
                col = (var_idx // n) % n
                row = var_idx // (n * n)
                solution[row][col] = num
        return solution, stats
    else:
        return None, stats

# Example usage:
if __name__ == "__main__":
    # 9x9 Sudoku example (0 represents empty cells)
    sudoku_9x9 = [
        [5, 3, 0, 0, 7, 0, 0, 0, 0],
        [6, 0, 0, 1, 9, 5, 0, 0, 0],
        [0, 9, 8, 0, 0, 0, 0, 6, 0],
        [8, 0, 0, 0, 6, 0, 0, 0, 3],
        [4, 0, 0, 8, 0, 3, 0, 0, 1],
        [7, 0, 0, 0, 2, 0, 0, 0, 6],
        [0, 6, 0, 0, 0, 0, 2, 8, 0],
        [0, 0, 0, 4, 1, 9, 0, 0, 5],
        [0, 0, 0, 0, 8, 0, 0, 7, 9]
    ]
    
    print("Solving 9x9 Sudoku with CDCL...")
    solution, stats = solve_sudoku_cdcl(sudoku_9x9)
    
    if solution:
        print("Solution found:")
        for row in solution:
            print(row)
    else:
        print("No solution exists")
    
    print(f"Decision steps: {stats['decision_steps']}")
    print(f"Unit propagations: {stats['unit_propagations']}")
    print(f"Learned clauses: {stats['learned_clauses']}")
    print(f"Time taken: {stats['time']:.4f} seconds")
