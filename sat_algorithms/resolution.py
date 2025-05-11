import re
import time
from itertools import combinations

class Literal:
    def __init__(self, name, negated=False):
        self.name = name
        self.negated = negated
    
    def __eq__(self, other):
        return self.name == other.name and self.negated == other.negated
    
    def __hash__(self):
        return hash((self.name, self.negated))
    
    def __str__(self):
        return f"¬{self.name}" if self.negated else self.name
    
    def __repr__(self):
        return str(self)
    
    def negate(self):
        return Literal(self.name, not self.negated)

class Clause:
    def __init__(self, literals):
        self.literals = frozenset(literals)
    
    def __eq__(self, other):
        return self.literals == other.literals
    
    def __hash__(self):
        return hash(self.literals)
    
    def __str__(self):
        return "{" + ", ".join(map(str, self.literals)) + "}"
    
    def __repr__(self):
        return str(self)
    
    def is_empty(self):
        return len(self.literals) == 0
    
    def is_tautology(self):
        literals = list(self.literals)
        for i in range(len(literals)):
            for j in range(i+1, len(literals)):
                if literals[i].name == literals[j].name and literals[i].negated != literals[j].negated:
                    return True
        return False
    
    def resolve(self, other):
        resolvents = set()
        for l1 in self.literals:
            for l2 in other.literals:
                if l1.name == l2.name and l1.negated != l2.negated:
                    new_literals = (self.literals - {l1}) | (other.literals - {l2})
                    new_clause = Clause(new_literals)
                    if not new_clause.is_tautology():
                        resolvents.add(new_clause)
        return resolvents

def parse_dimacs(dimacs_str):
    clauses = []
    lines = dimacs_str.split('\n')
    for line in lines:
        line = line.strip()
        if not line or line.startswith('c') or line.startswith('p'):
            continue
        literals = []
        for lit in line.split()[:-1]:  # Skip the 0 at the end
            lit = int(lit)
            if lit == 0:
                continue
            negated = lit < 0
            name = str(abs(lit))
            literals.append(Literal(name, negated))
        if literals:
            clauses.append(Clause(literals))
    return clauses

def parse_custom_format(clauses_str):
    clause_strs = re.findall(r'\{[^{}]+\}', clauses_str)
    clauses = []
    for cs in clause_strs:
        cs = re.sub(r'[{} ]', '', cs)
        literals = []
        for lit_str in cs.split(','):
            if lit_str.startswith('¬'):
                literals.append(Literal(lit_str[1:], True))
            else:
                literals.append(Literal(lit_str, False))
        clauses.append(Clause(literals))
    return clauses

def resolution_solver(clauses):
    clauses = [c for c in clauses if not c.is_tautology()]
    clauses = set(clauses)
    new = set()
    
    while True:
        for c1, c2 in combinations(clauses, 2):
            resolvents = c1.resolve(c2)
            for r in resolvents:
                if r.is_empty():
                    return False  # Unsatisfiable
                new.add(r)
        
        if new.issubset(clauses):
            return True  # Satisfiable
        
        clauses.update(new)
        new = set()

def get_input():
    print("Choose input format:")
    print("1. Custom format (e.g., {F1, ¬F2}, {F1, F3})")
    print("2. DIMACS format")
    choice = input("Enter choice (1 or 2): ").strip()
    
    print("\nEnter your clauses (type 'done' on a new line when finished):")
    input_lines = []
    while True:
        line = input().strip()
        if line.lower() == 'done':
            break
        input_lines.append(line)
    
    input_str = '\n'.join(input_lines)
    
    if choice == '1':
        return parse_custom_format(input_str)
    else:
        return parse_dimacs(input_str)

if __name__ == "__main__":
    clauses = get_input()
    
    print("\nParsed clauses:")
    for clause in clauses:
        print(clause)
    
    print("\nSolving...")
    start_time = time.time()
    result = resolution_solver(clauses)
    end_time = time.time()
    
    print("\nThe formula is", "satisfiable" if result else "unsatisfiable")
    print(f"Solving time: {end_time - start_time:.4f} seconds")
