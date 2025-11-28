MAX_CONSTANTS = 10

# ============================================================
#                      GLOBAL TOKEN SETS
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


# Parse a formula, consult parseOutputs for return values.
def parse(fmla):

    if not all(ch in ALLOWED_CHARS for ch in fmla):
        return 0 

    return 0

# Return the LHS of a binary connective formula
def lhs(fmla):
    return ''

# Return the connective symbol of a binary connective formula
def con(fmla):
    return ''

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    return ''


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
def is_prop_atom(f: str) -> bool:
    return f in PROP

def is_fol_atom(f: str) -> bool:
    if len(f) < 6 or f[0] not in PRED or f[1] != '(' or f[-1] != ')':
        return False
    
    terms = f[2:-1].split(',')

conn = str
left = str
right = str

def find_main_connective(f: str) -> tuple[conn, left,right]:
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
