# ============================================================
#                     GLOBAL VARIABLES
# ============================================================
AST_CACHE: dict[str, tuple | None] = {}
MAX_CONSTANTS = 10

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
    ast = AST_CACHE.get(fmla)
    if not ast:
        parse(fmla)
        ast = AST_CACHE.get(fmla)
    return [ast] if ast else []

#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
# ---- Initial branch ----
    branch = {
        'formulas': list(tableau[0]),
        'constants': set(),
        'gamma_used': {},
    }
    queue = [branch]
    unknown = False

    while queue:
        branch = queue.pop(0)
        formulas = branch['formulas']

        if is_branch_closed(formulas):
            continue

        formula, rule, data = select_expansion(formulas, branch)

        if formula is None:
            return 1  # satisfiable

        if rule == 'alpha':
            apply_alpha_expansion(formulas, branch, formula, data, queue)

        elif rule == 'beta':
            apply_beta_expansion(formulas, branch, formula, data, queue)

        elif rule == 'delta':
            if apply_delta_expansion(formulas, branch, formula, data, queue):
                unknown = True

        elif rule == 'gamma':
            apply_gamma_expansion(formulas, branch, formula, data, queue)

    return 2 if unknown else 0


# ============================================================
#                         PARSE HELPERS
# ============================================================
constructor = str
pred = str
terms = tuple[str, str]
prop = str
def parse_propositional_atom(f: str) -> tuple[constructor, prop] | None:
    return ('prop' , f) if f in PROP else None

def parse_predicate_atom(f: str) -> tuple[constructor, pred, terms] | None:
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
      universal:          ('forall', var, sub)
      existential:        ('exists', var, sub)
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
        quant = f[0]
        var = f[1]
        sub_ast = build_ast(f[2:])
        if not sub_ast:
            return None
        return ('forall', var, sub_ast) if quant == 'A' else ('exists', var, sub_ast)
        
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
    Map AST shape to the skeleton's parseOutputs indices (0?8):

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

    constructor = ast[0]

    if constructor == 'pred':
        return 1
    
    if constructor == 'prop':
        return 6

    if constructor == '~':
        sub_cls = classify(ast[1])
        if sub_cls in (6, 7, 8):
            return 7
        else:
            return 2

    if constructor == 'forall':
        return 3

    if constructor == 'exists':
        return 4

    if constructor in ('&', '\\/', '->'):
        left_cls = classify(ast[1])
        right_cls = classify(ast[2])
        if left_cls in (6, 7, 8) and right_cls in (6, 7, 8):
            return 8
        else:
            return 5

    return 0

# ============================================================
#                       SAT HELPERS
# ============================================================

def ast_to_formula(ast: tuple) -> str:
    constructor = ast[0]
    if constructor == 'prop':
        return ast[1]
    if constructor == 'pred':
        return ast[1] + '(' + ','.join(ast[2]) + ')'
    if constructor == '~':
        return '~' + ast_to_formula(ast[1])
    if constructor in ('&', '\\/', '->'):
        return '(' + ast_to_formula(ast[1]) + constructor + ast_to_formula(ast[2]) + ')'
    if constructor == 'forall':
        return 'A' + ast[1] + ast_to_formula(ast[2])
    if constructor == 'exists':
        return 'E' + ast[1] + ast_to_formula(ast[2])
    return ''

def is_atomic_formula(ast: tuple) -> bool:
    return ast[0] in ('prop', 'pred')

def is_literal_formula(ast: tuple) -> bool:
    return is_atomic_formula(ast) or (ast[0] == '~' and is_atomic_formula(ast[1]))

def literal_complement(lit: tuple) -> tuple:
    return lit[1] if lit[0] == '~' else ('~', lit)

def is_branch_closed(formulas: list[tuple]) -> bool:
    literals = [f for f in formulas if is_literal_formula(f)]
    seen = set(ast_to_formula(f) for f in literals)
    for lit in literals:
        if ast_to_formula(literal_complement(lit)) in seen:
            return True
    return False

def substitute_term(ast: tuple, variable: str, constant: str) -> tuple:
    constructor = ast[0]

    if constructor == 'pred':
        return (
            'pred',
            ast[1],
            tuple(constant if x == variable else x for x in ast[2]),
        )

    if constructor == 'prop':
        return ast

    if constructor in ('&', '\\/', '->'):
        return (
            constructor,
            substitute_term(ast[1], variable, constant),
            substitute_term(ast[2], variable, constant),
        )

    if constructor == '~':
        return ('~', substitute_term(ast[1], variable, constant))

    if constructor in ('forall', 'exists'):
        if ast[1] == variable:
            return ast
        return (constructor, ast[1], substitute_term(ast[2], variable, constant))

    return ast

def add_formula_to_branch(formulas: list[tuple], f: tuple) -> None:
    if f not in formulas:
        formulas.append(f)

def create_fresh_constant(constants: set[str]) -> str:
    n = 1
    while True:
        c = 'c' + str(n)
        if c not in constants:
            return c
        n += 1


# ========== Rule Matching ==========
def match_alpha_rule(ast: tuple):
    constructor = ast[0]

    # A & B
    if constructor == '&':
        return ('alpha', (ast[1], ast[2]))

    # ~(A \/ B)
    if constructor == '~' and ast[1][0] == '\\/':
        sub = ast[1]
        return ('alpha', (('~', sub[1]), ('~', sub[2])))

    # ~(A -> B)
    if constructor == '~' and ast[1][0] == '->':
        sub = ast[1]
        return ('alpha', (sub[1], ('~', sub[2])))

    # ~~A
    if constructor == '~' and ast[1][0] == '~':
        return ('alpha', (ast[1][1], None))

    return None

def match_beta_rule(ast: tuple):
    constructor = ast[0]

    # A \/ B
    if constructor == '\\/':
        return ('beta', (ast[1], ast[2]))

    # A -> B
    if constructor == '->':
        return ('beta', (('~', ast[1]), ast[2]))

    # ~(A & B)
    if constructor == '~' and ast[1][0] == '&':
        sub = ast[1]
        return ('beta', (('~', sub[1]), ('~', sub[2])))

    return None

def match_delta_rule(ast: tuple):
    constructor = ast[0]

    # Ex P(x)  ?  P(c/x)
    if constructor == 'exists':
        return ('delta', (False, ast[1], ast[2]))

    # ~Ax P(x) ? ~P(c/x)
    if constructor == '~' and ast[1][0] == 'forall':
        sub = ast[1]
        return ('delta', (True, sub[1], sub[2]))

    return None

def match_gamma_rule(ast: tuple, constants: set[str], gamma_used: dict):
    constructor = ast[0]

    # Ax P(x) ? P(c/x)
    if constructor == 'forall':
        variable, body = ast[1], ast[2]

    # ~Ex P(x)  ? ~P(c/x)
    elif constructor == '~' and ast[1][0] == 'exists':
        sub = ast[1]
        variable, body = sub[1], ('~', sub[2])

    else:
        return None

    used_constants = gamma_used.get(ast, set())

    # if no constants exist yet, introduce a fresh one
    if not constants:
        c = create_fresh_constant(constants)
        return ('gamma', (variable, body, c, True))

    # Otherwise, pick one that hasn't been used yet from the existing constants
    for c in constants:
        if c not in used_constants:
            return ('gamma', (variable, body, c, False))

    return None

# ========== Select expansion ==========

def select_expansion(formulas: list[tuple], branch: dict):
    for f in formulas:
        if is_literal_formula(f):
            continue

        res = match_alpha_rule(f)
        if res:
            return f, res[0], res[1]

        res = match_beta_rule(f)
        if res:
            return f, res[0], res[1]

        res = match_delta_rule(f)
        if res:
            return f, res[0], res[1]

        res = match_gamma_rule(f, branch['constants'], branch['gamma_used'])
        if res:
            return f, res[0], res[1]

    return None, None, None


# ========== Apply rule expansions  ==========

def apply_alpha_expansion(formulas, branch, formula, data, queue):
    left, right = data
    new_formulas = [g for g in formulas if g is not formula]
    if left:
        add_formula_to_branch(new_formulas, left)
    if right:
        add_formula_to_branch(new_formulas, right)
    queue.append({
        'formulas': new_formulas,
        'constants': set(branch['constants']),
        'gamma_used': {k: set(v) for k, v in branch['gamma_used'].items()},
    })

def apply_beta_expansion(formulas, branch, formula, data, queue):
    left, right = data
    for child in (left, right):
        new_formulas = [g for g in formulas if g is not formula]
        add_formula_to_branch(new_formulas, child)
        queue.append({
            'formulas': new_formulas,
            'constants': set(branch['constants']),
            'gamma_used': {k: set(v) for k, v in branch['gamma_used'].items()},
        })

def apply_delta_expansion(formulas, branch, formula, data, queue):
    is_negated_forall, variable, body = data

    new_const = create_fresh_constant(branch['constants'])
    new_constants = set(branch['constants'])
    new_constants.add(new_const)

    if len(new_constants) > MAX_CONSTANTS:
        return True

    instance = substitute_term(body, variable, new_const)
    if is_negated_forall:
        instance = ('~', instance)

    new_formulas = [g for g in formulas if g is not formula]
    add_formula_to_branch(new_formulas, instance)

    queue.append({
        'formulas': new_formulas,
        'constants': new_constants,
        'gamma_used': {k: set(v) for k, v in branch['gamma_used'].items()},
    })
    return False

def apply_gamma_expansion(formulas, branch, formula, data, queue):
    variable, body, const, is_new = data

    new_constants = set(branch['constants'])
    if is_new:
        new_constants.add(const)

    instance = substitute_term(body, variable, const)

    new_formulas = list(formulas)
    add_formula_to_branch(new_formulas, instance)

    new_gamma_used = {k: set(v) for k, v in branch['gamma_used'].items()}
    new_gamma_used.setdefault(formula, set()).add(const)

    queue.append({
        'formulas': new_formulas,
        'constants': new_constants,
        'gamma_used': new_gamma_used,
    })


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
