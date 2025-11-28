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

# Global AST cache
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


# =========================== Tableau SAT ===========================
def sat(tableau: list[list[tuple]]) -> int:
    # ========== Helper functions ==========

    def to_str(ast: tuple) -> str:
        k = ast[0]
        if k == 'prop':
            return ast[1]
        if k == 'pred':
            return ast[1] + '(' + ','.join(ast[2]) + ')'
        if k == '~':
            return '~' + to_str(ast[1])
        if k in ('&', '\\/', '->'):
            return '(' + to_str(ast[1]) + k + to_str(ast[2]) + ')'
        if k == 'forall':
            return 'A' + ast[1] + to_str(ast[2])
        if k == 'exists':
            return 'E' + ast[1] + to_str(ast[2])
        return ''

    def is_atom(ast: tuple) -> bool:
        return ast[0] in ('prop', 'pred')

    def is_literal(ast: tuple) -> bool:
        return is_atom(ast) or (ast[0] == '~' and is_atom(ast[1]))

    def complement(lit: tuple) -> tuple:
        return lit[1] if lit[0] == '~' else ('~', lit)

    def branch_closed(formulas: list[tuple]) -> bool:
        lits = [f for f in formulas if is_literal(f)]
        seen = set(to_str(f) for f in lits)
        for f in lits:
            if to_str(complement(f)) in seen:
                return True
        return False

    def collect_constants_from_formula(ast: tuple, consts: set[str]) -> None:
        k = ast[0]
        if k == 'pred':
            for t in ast[2]:
                if isinstance(t, str) and t.startswith('c'):
                    consts.add(t)
        elif k in ('&', '\\/', '->'):
            collect_constants_from_formula(ast[1], consts)
            collect_constants_from_formula(ast[2], consts)
        elif k == '~':
            collect_constants_from_formula(ast[1], consts)
        elif k in ('forall', 'exists'):
            collect_constants_from_formula(ast[2], consts)

    def initial_constants(formulas: list[tuple]) -> set[str]:
        consts: set[str] = set()
        for f in formulas:
            collect_constants_from_formula(f, consts)
        return consts

    def new_constant(constants: set[str]) -> str:
        n = 1
        while True:
            c = 'c' + str(n)
            if c not in constants:
                return c
            n += 1

    def substitute(ast: tuple, var: str, const: str) -> tuple:
        k = ast[0]
        if k == 'pred':
            return ('pred', ast[1],
                    tuple(const if x == var else x for x in ast[2]))
        if k == 'prop':
            return ast
        if k in ('&', '\\/', '->'):
            return (k,
                    substitute(ast[1], var, const),
                    substitute(ast[2], var, const))
        if k == '~':
            return ('~', substitute(ast[1], var, const))
        if k in ('forall', 'exists'):
            if ast[1] == var:
                return ast
            return (k, ast[1], substitute(ast[2], var, const))
        return ast

    def add_formula(formulas: list[tuple], f: tuple) -> None:
        if f not in formulas:
            formulas.append(f)

    # -------- classify α / β / δ / γ --------

    def alpha_children(ast: tuple) -> tuple | None:
        k = ast[0]
        if k == '&':
            return (ast[1], ast[2])
        if k == '~':
            sub = ast[1]
            if sub[0] == '\\/':
                return (('~', sub[1]), ('~', sub[2]))
            if sub[0] == '->':
                return (sub[1], ('~', sub[2]))
            if sub[0] == '~':
                # ¬¬A  →  A
                return (sub[1], None)
        return None

    def beta_children(ast: tuple) -> tuple | None:
        k = ast[0]
        if k == '\\/':
            return (ast[1], ast[2])
        if k == '->':
            return (('~', ast[1]), ast[2])
        if k == '~' and ast[1][0] == '&':
            sub = ast[1]
            return (('~', sub[1]), ('~', sub[2]))
        return None

    def is_delta(ast: tuple) -> tuple | None:
        k = ast[0]
        if k == 'exists':
            # ∃x φ(x)
            return ('exists', ast[1], ast[2])
        if k == '~' and ast[1][0] == 'forall':
            # ¬∀x φ(x)
            sub = ast[1]
            return ('not_forall', sub[1], sub[2])
        return None

    def gamma_info(ast: tuple, branch: dict) -> tuple | None:
        k = ast[0]
        if k == 'forall':
            # ∀x φ(x)
            var = ast[1]
            body = ast[2]
            gkind = 'forall'
        elif k == '~' and ast[1][0] == 'exists':
            # ¬∃x φ(x)   ≡   ∀x ¬φ(x)
            sub = ast[1]
            var = sub[1]
            body = sub[2]
            gkind = 'not_exists'
        else:
            return None

        constants: set[str] = branch['constants']
        used: set[str] = branch['gamma_used'].get(ast, set())

        # If there is no closed term yet, introduce one to start γ-expansion
        if not constants:
            c = new_constant(constants)
            return (gkind, var, body, c, True)

        # Otherwise pick a closed term not yet used for this γ-formula
        for c in constants:
            if c not in used:
                return (gkind, var, body, c, False)

        # All closed terms already used for this γ-formula
        return None

    # ========== Main tableau algorithm ==========

    if not tableau or not tableau[0]:
        return 0

    init_formulas: list[tuple] = list(tableau[0])
    init_constants: set[str] = initial_constants(init_formulas)

    init_branch: dict = {
        'formulas': init_formulas,       # list of ASTs
        'constants': init_constants,     # set of constant symbols 'c1', 'c2', ...
        'gamma_used': {}                 # map: γ-formula -> set of constants already used
    }

    # Queue of branches (theories), to ensure a fair schedule
    queue: list[dict] = [init_branch]

    # If we had to stop expansion on some open branch because of constant limit
    unknown: bool = False

    while queue:
        branch = queue.pop(0)
        formulas: list[tuple] = branch['formulas']

        # If branch already contains p and ¬p, skip it (closed)
        if branch_closed(formulas):
            continue

        # -------- Pick a formula to expand (α > β > δ > γ) --------
        chosen: tuple | None = None
        chosen_kind: str | None = None
        chosen_data: tuple | None = None

        for f in formulas:
            if is_literal(f):
                continue

            ac = alpha_children(f)
            if ac:
                chosen = f
                chosen_kind = 'alpha'
                chosen_data = ac
                break

            bc = beta_children(f)
            if bc:
                chosen = f
                chosen_kind = 'beta'
                chosen_data = bc
                break

            dc = is_delta(f)
            if dc:
                chosen = f
                chosen_kind = 'delta'
                chosen_data = dc
                break

            gi = gamma_info(f, branch)
            if gi:
                chosen = f
                chosen_kind = 'gamma'
                chosen_data = gi
                break

        # 没有任何非 literal 且还能展开的公式：open 且 fully expanded → SAT
        if chosen is None:
            return 1

        # -------- Apply the appropriate expansion --------

        # α-rule: single branch, replace ψ by its two α-children
        if chosen_kind == 'alpha':
            a1, a2 = chosen_data  # type: ignore
            new_formulas = [g for g in formulas if g is not chosen]
            if a1 is not None:
                add_formula(new_formulas, a1)
            if a2 is not None:
                add_formula(new_formulas, a2)

            new_branch = {
                'formulas': new_formulas,
                'constants': set(branch['constants']),
                'gamma_used': {k: set(v) for k, v in branch['gamma_used'].items()}
            }
            if not branch_closed(new_branch['formulas']):
                queue.append(new_branch)
            continue

        # β-rule: split into two branches
        if chosen_kind == 'beta':
            b1, b2 = chosen_data  # type: ignore
            for child in (b1, b2):
                new_formulas = [g for g in formulas if g is not chosen]
                add_formula(new_formulas, child)
                new_branch = {
                    'formulas': new_formulas,
                    'constants': set(branch['constants']),
                    'gamma_used': {k: set(v) for k, v in branch['gamma_used'].items()}
                }
                if not branch_closed(new_branch['formulas']):
                    queue.append(new_branch)
            continue

        # δ-rule: introduce a new constant (exists / not-forall)
        if chosen_kind == 'delta':
            kind_d, var_d, body_d = chosen_data  # type: ignore
            c = new_constant(branch['constants'])
            new_constants = set(branch['constants'])
            new_constants.add(c)

            # 超过 MAX_CONSTANTS，记为 unknown 分支
            if len(new_constants) > MAX_CONSTANTS:
                unknown = True
                continue

            if kind_d == 'exists':
                new_formula = substitute(body_d, var_d, c)
            else:  # 'not_forall'
                new_formula = ('~', substitute(body_d, var_d, c))

            new_formulas = [g for g in formulas if g is not chosen]
            add_formula(new_formulas, new_formula)

            new_branch = {
                'formulas': new_formulas,
                'constants': new_constants,
                'gamma_used': {k: set(v) for k, v in branch['gamma_used'].items()}
            }
            if not branch_closed(new_branch['formulas']):
                queue.append(new_branch)
            continue

        # γ-rule: use a closed term (or, if none yet, introduce one)
        if chosen_kind == 'gamma':
            gkind, var_g, body_g, c_g, is_new = chosen_data  # type: ignore

            new_constants = set(branch['constants'])
            if is_new:
                new_constants.add(c_g)
                if len(new_constants) > MAX_CONSTANTS:
                    unknown = True
                    continue

            # ∀x φ(x)  →  φ(c/x)
            # ¬∃x φ(x) →  ¬φ(c/x)
            if gkind == 'forall':
                instance = substitute(body_g, var_g, c_g)
            else:  # 'not_exists'
                instance = ('~', substitute(body_g, var_g, c_g))

            new_formulas = list(formulas)
            add_formula(new_formulas, instance)

            new_gamma_used = {k: set(v) for k, v in branch['gamma_used'].items()}
            used_consts = new_gamma_used.setdefault(chosen, set())
            used_consts.add(c_g)

            new_branch = {
                'formulas': new_formulas,
                'constants': new_constants,
                'gamma_used': new_gamma_used
            }
            if not branch_closed(new_branch['formulas']):
                queue.append(new_branch)
            continue

    # 所有分支都被关闭；如果过程中有因为常量上限被截断的 open 分支 → 2，否则 0
    return 2 if unknown else 0


# ==================== DO NOT MODIFY BELOW ====================

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