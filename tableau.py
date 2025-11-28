# ============================================================
#                      LEGAL TOKEN SETS
# ============================================================

# Propositional letters
PROP = {'p', 'q', 'r', 's'}

# FOL variables
VAR = {'x', 'y', 'z', 'w'}

# FOL predicate symbols (binary)
PRED = {'P', 'Q', 'R', 'S'}

# FOL quantifiers
QUANTIFIERS = {'A', 'E'}

# Unary connective
NEGATION = '~'

# Binary connectives (for clarity; we don't directly iterate this)
BINARY_CONNECTIVES = {'&', "\\/", "->"}

# Characters allowed to appear in input formulas
ALLOWED_CHARS = (
    PROP
    | VAR
    | PRED
    | QUANTIFIERS
    | set(NEGATION)
    | set(['(', ')', ',', '&', '\\', '/', '-', '>'])
)


# ============================================================
#                     GLOBAL VARIABLES
# ============================================================
AST_CACHE: dict[str, tuple | None] = {}
MAX_CONSTANTS = 10

# ============================================================
#                     Skeleton Functions
# ============================================================

# Parse a formula, consult parseOutputs for return values.
def parse(fmla):

    if not all(ch in ALLOWED_CHARS for ch in fmla):
        return 0 

    ast = build_ast(fmla)
    if ast is None:
        return 0
    
    AST_CACHE[fmla] = ast
    return classify(ast)

# Return the LHS of a binary connective formula
def lhs(fmla):
    res = find_main_connective(fmla)
    return res[1] if res else ''

# Return the connective symbol of a binary connective formula
def con(fmla):
    res = find_main_connective(fmla)
    return res[0] if res else ''
# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    res = find_main_connective(fmla)
    return res[2] if res else ''


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    return None

#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    return 0

# ============================================================
#                   PARSE HELPERS (TOP LEVEL)
# ============================================================
type = str
pred = str
terms = tuple[str, str]
prop = str
def parse_propositional_atom(f: str) -> tuple[type, prop] | None:
    return ('prop' , f) if f in PROP else None

def parse_predicate_atom(f: str) -> tuple[type, pred, terms] | None:
    if len(f) < 6 or f[0] not in PRED or f[1] != '(' or f[-1] != ')':
        return None
    
    terms = f[2:-1].split(',')
    if len(terms) != 2:
        return None
    
    t1, t2 = terms[0], terms[1]
    if t1 not in VAR or t2 not in VAR:
        return None

    return ('pred', f[0], (t1, t2))


conn = str
left = str
right = str
def find_main_connective(f: str) -> tuple[conn, left,right] | None:
    if len(f) < 5 or f[0] != '(' or f[-1] != ')':
        return None

    depth = 0
    for i, ch in enumerate(f):
        if ch == '(':
            depth += 1
            continue

        elif ch == ')':
            depth -= 1
            continue

        elif depth == 1:
            if f.startswith('\\/', i):
                return ('\\/', f[1:i], f[i+2:-1])
            if f.startswith('->', i):
                return ('->', f[1:i], f[i+2:-1])
            if ch == '&':
                return ('&', f[1:i], f[i+1:-1])
    return None

def build_ast(f:str) -> tuple | None:
    """
    Build an Abstract Syntax Tree (AST) for the formula s.
    Return AST (tuple) or None if s is not a well-formed formula.

    AST conventions:
      propositional atom: ('prop', 'p')
      predicate atom:     ('pred', 'P', ('x','y'))
      negation:           ('~', sub)
      binary connectives: ('&', left, right) / 
                          ('\\/', left, right) / 
                          ('->', left, right)
      universal:          ('A', var, sub)
      existential:        ('E', var, sub)
    """

    # Propositional atom
    prop = parse_propositional_atom(f)
    if prop:
        return prop
    
    # Predicate atom
    pred = parse_predicate_atom(f)
    if pred:
        return pred
    
    # Negation
    if f.startswith(NEGATION):
        sub_ast = build_ast(f[1:])
        if not sub_ast:
            return None
        return ('~', sub_ast)
    
    # Quantifiers
    if len(f) >= 3 and f[0] in QUANTIFIERS and f[1] in VAR:
        quantifier = f[0]
        var = f[1]
        sub_ast = build_ast(f[2:])
        if not sub_ast:
            return None
        return (quantifier, var, sub_ast)
        
    # Binary connectives
    res = find_main_connective(f)
    if res:
        conn, left, right = res
        left_ast = build_ast(left)
        right_ast = build_ast(right)
        if not left_ast or not right_ast:
            return None
        return (conn, left_ast, right_ast)
    
    return None

def classify(ast: tuple | None) -> int:
    """
    Map AST shape to the skeleton's parseOutputs indices (0–8):

    0: not a formula

    1: a first-order predicate atom
    2: a negation of a first order logic formula
    3: a universally quantified formula
    4: an existentially quantified formula
    5: a binary connective first order formula

    6: a propositional atom
    7: a negation of a propositional formula
    8: a binary connective propositional formula
    """
    if ast is None:
        return 0

    type = ast[0]

    if type == 'pred':
        return 1
    
    if type == 'prop':
        return 6

    if type == '~':
        sub_cls = classify(ast[1])
        if sub_cls in (6, 7, 8):
            return 7
        else:
            return 2

    if type == 'A':
        return 3

    if type == 'E':
        return 4

    if type in ('&', '\\/', '->'):
        left_cls = classify(ast[1])
        right_cls = classify(ast[2])
        if left_cls in (6, 7, 8) and right_cls in (6, 7, 8):
            return 8
        else:
            return 5

    return 0

#------------------------------------------------------------------------------------------------------------------------------:
#                                            DO NOT MODIFY THE CODE BELOW THIS LINE!                                           :
#------------------------------------------------------------------------------------------------------------------------------:

f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
