import time
from itertools import combinations
from copy import deepcopy

class DavisPutnam:
    def __init__(self):
        self.clauses = set()
        self.variables = set()
        self.assignments = {}
        self.stats = {
            "splitting_steps": 0,
            "unit_propagations": 0,
            "pure_eliminations": 0,
            "clauses": 0,
            "time": 0
        }

    def add_clause(self, clause):
        """Add a clause to the knowledge base"""
        self.clauses.add(frozenset(clause))
        for literal in clause:
            self.variables.add(abs(literal))

    def unit_propagate(self):
        """Perform unit propagation until no more unit clauses exist"""
        changed = True
        while changed:
            changed = False
            unit_clauses = [c for c in self.clauses if len(c) == 1]
            
            for clause in unit_clauses:
                self.stats["unit_propagations"] += 1
                literal = next(iter(clause))
                var = abs(literal)
                value = literal > 0
                
                # Skip if already assigned
                if var in self.assignments:
                    if self.assignments[var] != value:
                        return False  # Conflict
                    continue
                
                # Assign the variable
                self.assignments[var] = value
                
                # Remove all clauses containing this literal (they're satisfied)
                self.clauses = {c for c in self.clauses if literal not in c}
                
                # Remove negations of this literal from all clauses
                new_clauses = set()
                for c in self.clauses:
                    if -literal in c:
                        new_clause = c - {-literal}
                        if not new_clause:  # Empty clause found - conflict
                            return False
                        new_clauses.add(new_clause)
                    else:
                        new_clauses.add(c)
                self.clauses = new_clauses
                
                changed = True
        
        return True

    def pure_literal_elimination(self):
        """Eliminate pure literals from the formula"""
        literal_counts = {}
        for clause in self.clauses:
            for literal in clause:
                if literal in literal_counts:
                    literal_counts[literal] += 1
                else:
                    literal_counts[literal] = 1
        
        pure_literals = []
        for literal in literal_counts:
            if -literal not in literal_counts:
                pure_literals.append(literal)
        
        for literal in pure_literals:
            self.stats["pure_eliminations"] += 1
            var = abs(literal)
            value = literal > 0
            
            # Assign the pure literal
            if var not in self.assignments:
                self.assignments[var] = value
            
            # Remove all clauses containing this literal
            self.clauses = {c for c in self.clauses if literal not in c}

    def choose_variable(self):
        """Select an unassigned variable for splitting"""
        assigned_vars = set(self.assignments.keys())
        unassigned = [var for var in self.variables if var not in assigned_vars]
        if not unassigned:
            return None
        return unassigned[0]  # Simple heuristic - choose first unassigned

    def solve(self):
        """Execute the Davis-Putnam algorithm"""
        start_time = time.time()
        
        # Initial unit propagation and pure literal elimination
        if not self.unit_propagate():
            self.stats["time"] = time.time() - start_time
            self.stats["clauses"] = len(self.clauses)
            return False
        
        self.pure_literal_elimination()
        
        # If all clauses are satisfied, we're done
        if not self.clauses:
            self.stats["time"] = time.time() - start_time
            self.stats["clauses"] = len(self.clauses)
            return True
        
        # Choose a variable to split on
        var = self.choose_variable()
        if var is None:
            self.stats["time"] = time.time() - start_time
            self.stats["clauses"] = len(self.clauses)
            return True
        
        self.stats["splitting_steps"] += 1
        
        # Try assigning the variable to True
        solver_true = deepcopy(self)
        solver_true.clauses.add(frozenset([var]))
        if solver_true.solve():
            self.clauses = solver_true.clauses
            self.assignments = solver_true.assignments
            self.stats = solver_true.stats
            self.stats["time"] = time.time() - start_time
            return True
        
        # Try assigning the variable to False
        solver_false = deepcopy(self)
        solver_false.clauses.add(frozenset([-var]))
        if solver_false.solve():
            self.clauses = solver_false.clauses
            self.assignments = solver_false.assignments
            self.stats = solver_false.stats
            self.stats["time"] = time.time() - start_time
            return True
        
        self.stats["time"] = time.time() - start_time
        return False

    def get_stats(self):
        return self.stats

def encode_sudoku(sudoku_grid):
    """Encode a Sudoku puzzle as propositional clauses for Davis-Putnam"""
    n = len(sudoku_grid)
    sqrt_n = int(n ** 0.5)
    solver = DavisPutnam()
    
    # Each cell contains at least one number (1..n)
    for row in range(n):
        for col in range(n):
            clause = [row * n * n + col * n + num + 1 for num in range(n)]
            solver.add_clause(clause)
    
    # Each cell contains at most one number
    for row in range(n):
        for col in range(n):
            for num1, num2 in combinations(range(n), 2):
                solver.add_clause([-(row * n * n + col * n + num1 + 1), 
                                 -(row * n * n + col * n + num2 + 1)])
    
    # Each number appears at most once in each row
    for row in range(n):
        for num in range(n):
            for col1, col2 in combinations(range(n), 2):
                solver.add_clause([-(row * n * n + col1 * n + num + 1), 
                                 -(row * n * n + col2 * n + num + 1)])
    
    # Each number appears at most once in each column
    for col in range(n):
        for num in range(n):
            for row1, row2 in combinations(range(n), 2):
                solver.add_clause([-(row1 * n * n + col * n + num + 1), 
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
                    solver.add_clause([-(r1 * n * n + c1 * n + num + 1), 
                                      -(r2 * n * n + c2 * n + num + 1)])
    
    # Add pre-filled cells as unit clauses
    for row in range(n):
        for col in range(n):
            if sudoku_grid[row][col] != 0:
                num = sudoku_grid[row][col] - 1
                solver.add_clause([row * n * n + col * n + num + 1])
    
    return solver

def solve_sudoku_dp(sudoku_grid):
    """Solve a Sudoku puzzle using the Davis-Putnam algorithm"""
    solver = encode_sudoku(sudoku_grid)
    result = solver.solve()
    stats = solver.get_stats()
    
    if result:
        # Reconstruct the solution from the assignments
        n = len(sudoku_grid)
        solution = [[0 for _ in range(n)] for _ in range(n)]
        for var, value in solver.assignments.items():
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
    
    print("Solving 9x9 Sudoku with Davis-Putnam...")
    solution, stats = solve_sudoku_dp(sudoku_9x9)
    
    if solution:
        print("Solution found:")
        for row in solution:
            print(row)
    else:
        print("No solution exists")
    
    print(f"Splitting steps: {stats['splitting_steps']}")
    print(f"Unit propagations: {stats['unit_propagations']}")
    print(f"Pure eliminations: {stats['pure_eliminations']}")
    print(f"Clauses: {stats['clauses']}")
    print(f"Time taken: {stats['time']:.4f} seconds")
