MAX_CONSTANTS: int = 10

# Propositional letters
PROP: set[str] = {'p', 'q', 'r', 's'}

# FOL variables
VAR: set[str] = {'x', 'y', 'z', 'w'}

# FOL predicate symbols
PRED: set[str] = {'P', 'Q', 'R', 'S'}

# Quantifiers
QUANTIFIERS: set[str] = {'A', 'E'}

# Unary connective
NEGATION: str = '~'

# Allowed characters (no constants in input language)
ALLOWED_CHARS: set[str] = (
    PROP
    | VAR
    | PRED
    | QUANTIFIERS
    | {NEGATION}
    | set(['(', ')', ',', '&', '\\', '/', '-', '>'])
)

_ast_cache: dict[str, tuple | None] = {}


# ======================= Parse helpers =======================

def is_prop_atom(s: str) -> bool:
    return s in PROP


def parse_predicate(s: str) -> tuple | None:
    if len(s) < 4:
        return None
    if s[0] not in PRED:
        return None
    if s[1] != '(' or s[-1] != ')':
        return None
    body = s[2:-1]
    parts = body.split(',')
    if len(parts) != 2:
        return None
    if parts[0] not in VAR or parts[1] not in VAR:
        return None
    return ('pred', s[0], (parts[0], parts[1]))


def find_main_connective(f: str) -> tuple[str, str, str] | None:
    if len(f) < 5 or f[0] != '(' or f[-1] != ')':
        return None
    depth: int = 0
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


# =========================== Build AST ===========================

def build_ast(s: str) -> tuple | None:
    s = s.strip()
    if s == '':
        return None
    if is_prop_atom(s):
        return ('prop', s)
    pred = parse_predicate(s)
    if pred:
        return pred
    if s.startswith(NEGATION):
        sub = build_ast(s[1:])
        if not sub:
            return None
        return ('~', sub)
    if len(s) >= 3 and s[0] in QUANTIFIERS and s[1] in VAR:
        quant = s[0]
        var = s[1]
        sub = build_ast(s[2:])
        if not sub:
            return None
        return ('forall', var, sub) if quant == 'A' else ('exists', var, sub)
    res = find_main_connective(s)
    if res:
        conn, left_s, right_s = res
        left = build_ast(left_s)
        right = build_ast(right_s)
        if left and right:
            return (conn, left, right)
    return None


# =========================== Classify AST ===========================

def classify(ast: tuple | None) -> int:
    if ast is None:
        return 0
    k = ast[0]
    if k == 'prop':
        return 6
    if k == 'pred':
        return 1
    if k == '~':
        sub_cls = classify(ast[1])
        return 7 if sub_cls in (6, 7, 8) else 2
    if k == 'forall':
        return 3
    if k == 'exists':
        return 4
    if k in ('&', '\\/', '->'):
        l = classify(ast[1])
        r = classify(ast[2])
        return 8 if l in (6, 7, 8) and r in (6, 7, 8) else 5
    return 0


# =========================== Parse ===========================

def parse(fmla: str) -> int:
    for ch in fmla:
        if ch not in ALLOWED_CHARS:
            return 0
    ast = build_ast(fmla)
    if not ast:
        return 0
    _ast_cache[fmla] = ast
    return classify(ast)


# ======================= Binary accessors =======================

def lhs(fmla: str) -> str:
    res = find_main_connective(fmla)
    return res[1] if res else ''


def con(fmla: str) -> str:
    res = find_main_connective(fmla)
    return res[0] if res else ''


def rhs(fmla: str) -> str:
    res = find_main_connective(fmla)
    return res[2] if res else ''


# =========================== Theory ===========================

def theory(fmla: str) -> list[tuple]:
    ast = _ast_cache.get(fmla)
    if not ast:
        parse(fmla)
        ast = _ast_cache.get(fmla)
    return [ast] if ast else []


# ===================== Tableau Helper Functions =====================

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


# ========== Rule Matching (α / β / δ / γ) ==========

def match_alpha_rule(ast: tuple):
    constructor = ast[0]

    if constructor == '&':
        return ('alpha', (ast[1], ast[2]))

    if constructor == '~' and ast[1][0] == '\\/':
        sub = ast[1]
        return ('alpha', (('~', sub[1]), ('~', sub[2])))

    if constructor == '~' and ast[1][0] == '->':
        sub = ast[1]
        return ('alpha', (sub[1], ('~', sub[2])))

    if constructor == '~' and ast[1][0] == '~':
        return ('alpha', (ast[1][1], None))

    return None


def match_beta_rule(ast: tuple):
    constructor = ast[0]

    if constructor == '\\/':
        return ('beta', (ast[1], ast[2]))

    if constructor == '->':
        return ('beta', (('~', ast[1]), ast[2]))

    if constructor == '~' and ast[1][0] == '&':
        sub = ast[1]
        return ('beta', (('~', sub[1]), ('~', sub[2])))

    return None


def match_delta_rule(ast: tuple):
    constructor = ast[0]

    if constructor == 'exists':
        return ('delta', (False, ast[1], ast[2]))

    if constructor == '~' and ast[1][0] == 'forall':
        sub = ast[1]
        return ('delta', (True, sub[1], sub[2]))

    return None


def match_gamma_rule(ast: tuple, constants: set[str], gamma_used: dict):
    constructor = ast[0]

    if constructor == 'forall':
        variable, body = ast[1], ast[2]

    elif constructor == '~' and ast[1][0] == 'exists':
        sub = ast[1]
        variable, body = sub[1], ('~', sub[2])

    else:
        return None

    used = gamma_used.get(ast, set())

    if not constants:
        c = create_fresh_constant(constants)
        return ('gamma', (variable, body, c, True))

    for c in constants:
        if c not in used:
            return ('gamma', (variable, body, c, False))

    return None


# ========== Select expansion (抽出第一步重构核心) ==========

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


# ========== Apply rule expansions (抽出第二步重构核心) ==========

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


# =========================== Tableau SAT (精简后的主体) ===========================

def sat(tableau: list[list[tuple]]) -> int:
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


# ==================== DO NOT MODIFY BELOW THIS LINE ====================


# f = open('input.txt')
# f = open('testSet2.txt')
f = open('testSet/testSet3.txt')
# f = open('testSet/testSet4.txt')

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
        if parsed in [5, 8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (
                lhs(line), con(line), rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
