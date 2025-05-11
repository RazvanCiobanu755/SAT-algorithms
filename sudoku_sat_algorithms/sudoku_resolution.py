import time
from itertools import combinations

class DPLL:
    def __init__(self):
        self.clauses = set()
        self.variables = set()
        self.assignments = {}
        self.decision_steps = 0
        self.unit_propagations = 0

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
                self.unit_propagations += 1
                literal = next(iter(clause))
                var = abs(literal)
                value = literal > 0
                
                # Add the assignment
                self.assignments[var] = value
                
                # Remove all clauses containing this literal (they're satisfied)
                self.clauses = {c for c in self.clauses if literal not in c}
                
                # Remove negations of this literal from all clauses
                new_clauses = set()
                for c in self.clauses:
                    if -literal in c:
                        new_clause = c - {-literal}
                        if not new_clause:  # Empty clause found
                            return False
                        new_clauses.add(new_clause)
                    else:
                        new_clauses.add(c)
                
                self.clauses = new_clauses
                changed = True
        
        return True

    def choose_literal(self):
        """Select an unassigned variable using some heuristic"""
        unassigned = [var for var in self.variables if var not in self.assignments]
        return unassigned[0] if unassigned else None

    def solve(self):
        """Execute the DPLL algorithm with backtracking"""
        # First, perform unit propagation
        if not self.unit_propagate():
            return False
        
        # If all clauses are satisfied, we're done
        if not self.clauses:
            return True
        
        # Choose a literal to branch on
        literal = self.choose_literal()
        if literal is None:
            return False  # Shouldn't happen if problem is satisfiable
        
        self.decision_steps += 1
        
        # Try assigning the literal to True
        self.assignments[literal] = True
        new_clauses_true = set()
        for c in self.clauses:
            if -literal in c:
                new_clause = c - {-literal}
                if not new_clause:  # Empty clause found
                    break
                new_clauses_true.add(new_clause)
            else:
                new_clauses_true.add(c)
        
        old_clauses = self.clauses
        self.clauses = new_clauses_true
        if self.solve():
            return True
        self.clauses = old_clauses
        del self.assignments[literal]
        
        # Try assigning the literal to False
        self.assignments[literal] = False
        new_clauses_false = set()
        for c in self.clauses:
            if literal in c:
                new_clause = c - {literal}
                if not new_clause:  # Empty clause found
                    break
                new_clauses_false.add(new_clause)
            else:
                new_clauses_false.add(c)
        
        self.clauses = new_clauses_false
        result = self.solve()
        self.clauses = old_clauses
        if not result:
            del self.assignments[literal]
        return result

    def get_stats(self):
        return {
            "decision_steps": self.decision_steps,
            "unit_propagations": self.unit_propagations,
            "clauses": len(self.clauses),
            "assignments": len(self.assignments)
        }

def encode_sudoku(sudoku_grid):
    """Encode a Sudoku puzzle as propositional clauses for DPLL"""
    n = len(sudoku_grid)
    sqrt_n = int(n ** 0.5)
    dpll = DPLL()
    
    # Each cell contains at least one number (1..n)
    for row in range(n):
        for col in range(n):
            clause = [row * n * n + col * n + num + 1 for num in range(n)]
            dpll.add_clause(clause)
    
    # Each cell contains at most one number
    for row in range(n):
        for col in range(n):
            for num1, num2 in combinations(range(n), 2):
                dpll.add_clause([-(row * n * n + col * n + num1 + 1), 
                               -(row * n * n + col * n + num2 + 1)])
    
    # Each number appears at most once in each row
    for row in range(n):
        for num in range(n):
            for col1, col2 in combinations(range(n), 2):
                dpll.add_clause([-(row * n * n + col1 * n + num + 1), 
                               -(row * n * n + col2 * n + num + 1)])
    
    # Each number appears at most once in each column
    for col in range(n):
        for num in range(n):
            for row1, row2 in combinations(range(n), 2):
                dpll.add_clause([-(row1 * n * n + col * n + num + 1), 
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
                    dpll.add_clause([-(r1 * n * n + c1 * n + num + 1), 
                                    -(r2 * n * n + c2 * n + num + 1)])
    
    # Add pre-filled cells as unit clauses
    for row in range(n):
        for col in range(n):
            if sudoku_grid[row][col] != 0:
                num = sudoku_grid[row][col] - 1
                dpll.add_clause([row * n * n + col * n + num + 1])
    
    return dpll

def solve_sudoku_dpll(sudoku_grid):
    """Solve a Sudoku puzzle using the DPLL algorithm"""
    dpll = encode_sudoku(sudoku_grid)
    start_time = time.time()
    result = dpll.solve()
    end_time = time.time()
    
    stats = dpll.get_stats()
    stats['time'] = end_time - start_time
    
    if result:
        # Reconstruct the solution from the assignments
        n = len(sudoku_grid)
        solution = [[0 for _ in range(n)] for _ in range(n)]
        for var, value in dpll.assignments.items():
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
    sudoku_9x9 =   [
    [8, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 3, 6, 0, 0, 0, 0, 0],
    [0, 7, 0, 0, 9, 0, 2, 0, 0],
    [0, 5, 0, 0, 0, 7, 0, 0, 0],
    [0, 0, 0, 0, 4, 5, 7, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 3, 0],
    [0, 0, 1, 0, 0, 0, 0, 6, 8],
    [0, 0, 8, 5, 0, 0, 0, 1, 0],
    [0, 9, 0, 0, 0, 0, 4, 0, 0]
]
    print("Solving 9x9 Sudoku with DPLL...")
    solution, stats = solve_sudoku_dpll(sudoku_9x9)
    
    if solution:
        print("Solution found:")
        for row in solution:
            print(row)
    else:
        print("No solution exists")
    
    print(f"Decision steps: {stats['decision_steps']}")
    print(f"Unit propagations: {stats['unit_propagations']}")
    print(f"Time taken: {stats['time']:.4f} seconds")
