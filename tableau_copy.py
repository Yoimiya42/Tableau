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

# Binary connectives
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
#                   PARSE HELPERS (TOP LEVEL)
# ============================================================

def is_prop_atom(s):
    # A propositional atom must be exactly one of p,q,r,s
    return s in PROP


def parse_predicate(s):
    # PRED(var,var) where PRED in {P,Q,R,S} and var in {x,y,z,w}
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

    arg1, arg2 = parts[0], parts[1]
    if arg1 not in VAR or arg2 not in VAR:
        return None

    return ('pred', s[0], (arg1, arg2))


def strip_parens(s):
    # Remove a single pair of outermost brackets if they wrap exactly the string
    if len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        depth = 0
        for i, ch in enumerate(s):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if depth == 0 and i != len(s) - 1:
                # Outer () not matching the entire string
                return s
        # Proper outermost () wrapping whole s
        return s[1:-1]
    return s


def find_main_connective(s):
    depth = 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == '(':
            depth += 1
            i += 1
            continue
        if ch == ')':
            depth -= 1
            i += 1
            continue
        if depth == 0:
            # implication
            if s.startswith('->', i):
                return i, '->'
            # disjunction
            if s.startswith('\\/', i):
                return i, '\\/'
            # conjunction
            if ch == '&':
                return i, '&'
        i += 1
    return None, None


# ============================================================
#                         PARSE FORMULA
# ============================================================

def parse_formula(s, binary_cache):
    s = s.strip()
    if s == '':
        return None, 0

    # Propositional atom
    if is_prop_atom(s):
        return ('prop', s), 6

    # Predicate atom
    pred = parse_predicate(s)
    if pred:
        return pred, 1

    # Negation
    if s.startswith('~'):
        sub, cls = parse_formula(s[1:], binary_cache)
        if not sub:
            return None, 0
        if cls in [6, 7, 8]:
            # negation of propositional formula
            return ('not', sub), 7
        else:
            # negation of first-order formula
            return ('not', sub), 2

    # Quantifiers: Avar or Evar
    if len(s) >= 3 and s[0] in ['A', 'E'] and s[1] in VAR:
        quant = s[0]
        var = s[1]
        sub_fmla, sub_cls = parse_formula(s[2:], binary_cache)
        if not sub_fmla:
            return None, 0
        node = ('forall', var, sub_fmla) if quant == 'A' else ('exists', var, sub_fmla)
        return node, 3 if quant == 'A' else 4

    # Binary connective
    s_inner = strip_parens(s)
    idx, conn = find_main_connective(s_inner)
    if conn:
        left_s = s_inner[:idx]
        right_s = s_inner[idx + len(conn):]
        left, left_cls = parse_formula(left_s, binary_cache)
        right, right_cls = parse_formula(right_s, binary_cache)
        if not left or not right:
            return None, 0

        if conn == '->':
            node = ('imp', left, right)
        elif conn == '&':
            node = ('and', left, right)
        else:  # '\\/'
            node = ('or', left, right)

        # classify as propositional or first-order binary
        if left_cls in [6, 7, 8] and right_cls in [6, 7, 8]:
            classification = 8  # binary connective propositional formula
        else:
            classification = 5  # binary connective first-order formula

        binary_cache[s] = (left_s, conn, right_s)
        return node, classification

    return None, 0


# ============================================================
#                             PARSE
# ============================================================

def parse(fmla):
    global _binary_cache
    _binary_cache = getattr(parse, '_binary_cache', {})

    # Reject any illegal character (enforces: no whitespace, no extra symbols)
    for ch in fmla:
        if ch not in ALLOWED_CHARS:
            return 0

    ast, classification = parse_formula(fmla, _binary_cache)

    parse._binary_cache = _binary_cache
    parse._ast_cache = getattr(parse, '_ast_cache', {})
    parse._ast_cache[fmla] = ast
    return classification


# ============================================================
#                 BINARY CACHE ACCESSORS
# ============================================================

def lhs(fmla):
    cache = getattr(parse, '_binary_cache', {})
    return cache.get(fmla, ('', '', ''))[0]


def con(fmla):
    cache = getattr(parse, '_binary_cache', {})
    return cache.get(fmla, ('', '', ''))[1]


def rhs(fmla):
    cache = getattr(parse, '_binary_cache', {})
    return cache.get(fmla, ('', '', ''))[2]






# ============================================================
#                           THEORY
# ============================================================

def theory(fmla):
    # initialise a theory with a single formula in it
    ast = getattr(parse, '_ast_cache', {}).get(fmla)
    if not ast:
        parse(fmla)
        ast = getattr(parse, '_ast_cache', {}).get(fmla)
    return [ast] if ast else []


# ============================================================
#                        TABLEAU SAT
# ============================================================

def sat(tableau):
    # output 0 if not satisfiable, 1 if satisfiable, 2 if too many constants

    # ---------- AST → string ----------
    def to_str(ast):
        k = ast[0]
        if k == 'prop':
            return ast[1]
        if k == 'pred':
            return ast[1] + '(' + ','.join(ast[2]) + ')'
        if k == 'not':
            return '~' + to_str(ast[1])
        if k == 'and':
            return '(' + to_str(ast[1]) + '&' + to_str(ast[2]) + ')'
        if k == 'or':
            return '(' + to_str(ast[1]) + '\\/' + to_str(ast[2]) + ')'
        if k == 'imp':
            return '(' + to_str(ast[1]) + '->' + to_str(ast[2]) + ')'
        if k == 'forall':
            return 'A' + ast[1] + to_str(ast[2])
        if k == 'exists':
            return 'E' + ast[1] + to_str(ast[2])

    # ---------- substitution ----------
    def substitute(ast, var, const):
        k = ast[0]
        if k == 'pred':
            new_terms = tuple(const if t == var else t for t in ast[2])
            return ('pred', ast[1], new_terms)
        if k == 'prop':
            return ast
        if k in ('and', 'or', 'imp'):
            return (k, substitute(ast[1], var, const),
                       substitute(ast[2], var, const))
        if k == 'not':
            return ('not', substitute(ast[1], var, const))
        if k in ('forall', 'exists'):
            if ast[1] == var:
                return ast
            return (k, ast[1], substitute(ast[2], var, const))
        return ast

    # ---------- literals ----------
    def is_atom(ast):
        return ast[0] in ('prop', 'pred')

    def is_literal(ast):
        return is_atom(ast) or (ast[0] == 'not' and is_atom(ast[1]))

    def complement(lit):
        if lit[0] == 'not':
            return lit[1]
        return ('not', lit)

    def branch_closed(lits):
        lit_set = set(to_str(l) for l in lits)
        for l in lits:
            if to_str(complement(l)) in lit_set:
                return True
        return False

    # ---------- constants ----------
    def add_constant(branch, const):
        if const not in branch['constants']:
            branch['constants'].append(const)
            if len(branch['constants']) > MAX_CONSTANTS:
                return False
            for u in branch['universals']:
                key = to_str(u)
                used = branch['forall_used'].setdefault(key, set())
                if const not in used:
                    branch['pending'].append(substitute(u[2], u[1], const))
                    used.add(const)
        return True

    # ---------- clone branch ----------
    def clone_branch(br, extra_pending=None):
        return {
            'pending': br['pending'][:] + (extra_pending or []),
            'lits': br['lits'][:],
            'constants': br['constants'][:],
            'universals': br['universals'][:],
            'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
        }

    # ========================================================
    #                    EXPANSION RULES
    # ========================================================

    # α rules: ∧, ¬¬, ¬∨, ¬→
    def expand_alpha(br, f):
        k = f[0]

        # (φ & ψ)
        if k == 'and':
            br['pending'].extend([f[1], f[2]])
            return True

        if k == 'not':
            sub = f[1]
            sk = sub[0]

            # ¬¬φ
            if sk == 'not':
                br['pending'].append(sub[1])
                return True

            # ¬(φ ∨ ψ)
            if sk == 'or':
                br['pending'].append(('not', sub[1]))
                br['pending'].append(('not', sub[2]))
                return True

            # ¬(φ → ψ)
            if sk == 'imp':
                br['pending'].append(sub[1])
                br['pending'].append(('not', sub[2]))
                return True

        return False

    # β rules: ∨, →, ¬∧
    def expand_beta(br, f, branches):
        k = f[0]

        # (φ ∨ ψ)
        if k == 'or':
            branches.append(clone_branch(br, [f[1]]))
            branches.append(clone_branch(br, [f[2]]))
            return True

        # (φ → ψ)
        if k == 'imp':
            left, right = f[1], f[2]
            branches.append(clone_branch(br, [('not', left)]))
            branches.append(clone_branch(br, [right]))
            return True

        # ¬(φ ∧ ψ)
        if k == 'not' and f[1][0] == 'and':
            sub = f[1]
            branches.append(clone_branch(br, [('not', sub[1])]))
            branches.append(clone_branch(br, [('not', sub[2])]))
            return True

        return False

    # Negation rules for quantifiers: ¬∀, ¬∃
    def expand_negation(br, f):
        sub = f[1]
        sk = sub[0]

        # ¬∀x φ  ≡ ∃x ¬φ
        if sk == 'forall':
            br['pending'].append(('exists', sub[1], ('not', sub[2])))
            return True

        # ¬∃x φ ≡ ∀x ¬φ
        if sk == 'exists':
            br['pending'].append(('forall', sub[1], ('not', sub[2])))
            return True

        return False

    # γ rule: ∀
    def expand_gamma(br, f):
        if f not in br['universals']:
            br['universals'].append(f)

        key = to_str(f)
        used = br['forall_used'].setdefault(key, set())

        if not br['constants']:
            if not add_constant(br, 'c1'):
                return 2

        for const in list(br['constants']):
            if const not in used:
                br['pending'].append(substitute(f[2], f[1], const))
                used.add(const)

        return True

    # δ rule: ∃
    def expand_delta(br, f):
        new_const = 'c' + str(len(br['constants']) + 1)
        if not add_constant(br, new_const):
            return 2
        br['pending'].append(substitute(f[2], f[1], new_const))
        return True

    # ========================================================
    #                     INITIAL BRANCH
    # ========================================================

    branches = []
    initial_constants = set()

    def collect_constants(ast):
        k = ast[0]
        if k == 'pred':
            for t in ast[2]:
                # constants in input formulas would be uppercase or start with 'c'
                if t.isupper() or t.startswith('c'):
                    initial_constants.add(t)
        elif k in ('and', 'or', 'imp'):
            collect_constants(ast[1])
            collect_constants(ast[2])
        elif k == 'not':
            collect_constants(ast[1])
        elif k in ('forall', 'exists'):
            collect_constants(ast[2])

    for ast in tableau[0]:
        collect_constants(ast)

    if not initial_constants:
        initial_constants.add('c1')

    init_branch = {
        'pending': list(tableau[0]),
        'lits': [],
        'constants': list(initial_constants),
        'universals': [],
        'forall_used': {}
    }
    branches.append(init_branch)

    # ========================================================
    #                   MAIN TABLEAU LOOP
    # ========================================================

    while branches:
        br = branches.pop()

        while br['pending']:
            f = br['pending'].pop()

            # literals
            if is_literal(f):
                if branch_closed(br['lits'] + [f]):
                    br = None
                    break
                br['lits'].append(f)
                continue

            k = f[0]

            # α rules
            if expand_alpha(br, f):
                continue

            # β rules
            if expand_beta(br, f, branches):
                br = None
                break

            # negation of quantifiers
            if k == 'not':
                if expand_negation(br, f):
                    continue

            # γ rule: ∀
            if k == 'forall':
                r = expand_gamma(br, f)
                if r == 2:
                    return 2
                continue

            # δ rule: ∃
            if k == 'exists':
                r = expand_delta(br, f)
                if r == 2:
                    return 2
                continue

        if br is None:
            continue

        if branch_closed(br['lits']):
            continue
        if len(br['constants']) > MAX_CONSTANTS:
            return 2

        return 1

    return 0


# ============================================================
#              DO NOT MODIFY THE CODE BELOW THIS LINE!
# ============================================================

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
    if line and line[-1] == '\n':
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
