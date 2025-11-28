MAX_CONSTANTS = 10

# ============================================================
#                   PARSE HELPERS (TOP LEVEL)
# ============================================================

def is_prop_atom(s):
    return len(s) == 1 and s.islower()


def parse_predicate(s):
    if len(s) < 4 or not s[0].isupper() or s[1] != '(' or s[-1] != ')':
        return None
    body = s[2:-1]
    if body == '':
        return None
    terms = body.split(',')
    for term in terms:
        if not term.isalnum():
            return None
    return ('pred', s[0], tuple(terms))


def strip_parens(s):
    if len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        depth = 0
        for i, ch in enumerate(s):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if depth == 0 and i != len(s) - 1:
                return s
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
            if s.startswith('->', i):
                return i, '->'
            if s.startswith('\\/', i):
                return i, '\\/'
            if ch == '&':
                return i, '&'
        i += 1
    return None, None


# ============================================================
#                       PARSE FORMULA
# ============================================================

def parse_formula(s, binary_cache):
    s = s.strip()
    if s == '':
        return None, 0

    # proposition
    if is_prop_atom(s):
        return ('prop', s), 6

    # predicate
    pred = parse_predicate(s)
    if pred:
        return pred, 1

    # negation
    if s.startswith('~'):
        sub, cls = parse_formula(s[1:], binary_cache)
        if not sub:
            return None, 0
        if cls in [6, 7, 8]:
            return ('not', sub), 7
        else:
            return ('not', sub), 2

    # quantifier
    if len(s) >= 3 and s[0] in ['A', 'E'] and s[1].islower():
        quant = s[0]
        var = s[1]
        sub_fmla, sub_cls = parse_formula(s[2:], binary_cache)
        if not sub_fmla:
            return None, 0
        node = ('forall', var, sub_fmla) if quant == 'A' else ('exists', var, sub_fmla)
        return node, 3 if quant == 'A' else 4

    # binary connective
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
        else:
            node = ('or', left, right)

        classification = (
            8 if left_cls in [6, 7, 8] and right_cls in [6, 7, 8] else 5
        )
        binary_cache[s] = (left_s, conn, right_s)
        return node, classification

    return None, 0


# ============================================================
#                             PARSE
# ============================================================

def parse(fmla):
    global _binary_cache
    _binary_cache = getattr(parse, '_binary_cache', {})

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
#                         THEORY
# ============================================================

def theory(fmla):
    ast = getattr(parse, '_ast_cache', {}).get(fmla)
    if not ast:
        parse(fmla)
        ast = getattr(parse, '_ast_cache', {}).get(fmla)
    return [ast] if ast else []


# ============================================================
#                        TABLEAU SAT
# ============================================================

def sat(tableau):

    # ---------- AST → str ----------
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
            return ('pred', ast[1],
                    tuple(const if t == var else t for t in ast[2]))
        if k == 'prop':
            return ast
        if k in ('and', 'or', 'imp'):
            return (
                k,
                substitute(ast[1], var, const),
                substitute(ast[2], var, const),
            )
        if k == 'not':
            return ('not', substitute(ast[1], var, const))
        if k in ('forall', 'exists'):
            if ast[1] == var:
                return ast
            return (k, ast[1], substitute(ast[2], var, const))
        return ast

    # ---------- literal tests ----------
    def is_atom(ast):
        return ast[0] in ('prop', 'pred')

    def is_literal(ast):
        return (is_atom(ast) or
                (ast[0] == 'not' and is_atom(ast[1])))

    def complement(l):
        return l[1] if l[0] == 'not' else ('not', l)

    def branch_closed(lits):
        litset = set(to_str(l) for l in lits)
        for l in lits:
            if to_str(complement(l)) in litset:
                return True
        return False

    # ---------- constants ----------
    def add_constant(br, c):
        if c not in br['constants']:
            br['constants'].append(c)
            if len(br['constants']) > MAX_CONSTANTS:
                return False
            for u in br['universals']:
                key = to_str(u)
                used = br['forall_used'].setdefault(key, set())
                if c not in used:
                    br['pending'].append(
                        substitute(u[2], u[1], c)
                    )
                    used.add(c)
        return True

    # ---------- clone branch ----------
    def clone_branch(br, extra=None):
        return {
            'pending': br['pending'][:] + (extra or []),
            'lits': br['lits'][:],
            'constants': br['constants'][:],
            'universals': br['universals'][:],
            'forall_used': {
                k: set(v) for k, v in br['forall_used'].items()
            }
        }

    # ============================================================
    #                    EXPANSION RULES
    # ============================================================

    # ---------- α rules ----------
    def expand_alpha(br, f):
        k = f[0]

        if k == 'and':
            br['pending'].extend([f[1], f[2]])
            return True

        if k == 'not':
            sub = f[1]
            sk = sub[0]

            if sk == 'not':
                br['pending'].append(sub[1])
                return True
            if sk == 'or':
                br['pending'].append(('not', sub[1]))
                br['pending'].append(('not', sub[2]))
                return True
            if sk == 'imp':
                br['pending'].append(sub[1])
                br['pending'].append(('not', sub[2]))
                return True
        return False

    # ---------- β rules ----------
    def expand_beta(br, f, branches):
        k = f[0]

        if k == 'or':
            branches.append(clone_branch(br, [f[1]]))
            branches.append(clone_branch(br, [f[2]]))
            return True

        if k == 'imp':
            branches.append(clone_branch(br, [('not', f[1][0] and f[1] or f[1])]))
            branches.append(clone_branch(br, [f[2]]))
            return True

        if k == 'not' and f[1][0] == 'and':
            sub = f[1]
            branches.append(clone_branch(br, [('not', sub[1])]))
            branches.append(clone_branch(br, [('not', sub[2])]))
            return True

        return False

    # ---------- negation rules (quantifiers) ----------
    def expand_negation(br, f):
        sub = f[1]
        sk = sub[0]

        if sk == 'forall':
            br['pending'].append(('exists', sub[1], ('not', sub[2])))
            return True

        if sk == 'exists':
            br['pending'].append(('forall', sub[1], ('not', sub[2])))
            return True

        return False

    # ---------- γ (∀) ----------
    def expand_gamma(br, f):
        if f not in br['universals']:
            br['universals'].append(f)

        key = to_str(f)
        used = br['forall_used'].setdefault(key, set())

        if not br['constants']:
            if not add_constant(br, 'c1'):
                return 2

        for c in list(br['constants']):
            if c not in used:
                br['pending'].append(substitute(f[2], f[1], c))
                used.add(c)

        return True

    # ---------- δ (∃) ----------
    def expand_delta(br, f):
        newc = 'c' + str(len(br['constants']) + 1)
        if not add_constant(br, newc):
            return 2
        br['pending'].append(substitute(f[2], f[1], newc))
        return True

    # ============================================================
    #                       INITIAL BRANCH
    # ============================================================

    branches = []
    init_consts = set()

    def collect_consts(ast):
        k = ast[0]
        if k == 'pred':
            for t in ast[2]:
                if t.isupper() or t.startswith('c'):
                    init_consts.add(t)
        elif k in ('and', 'or', 'imp'):
            collect_consts(ast[1])
            collect_consts(ast[2])
        elif k == 'not':
            collect_consts(ast[1])
        elif k in ('forall', 'exists'):
            collect_consts(ast[2])

    for a in tableau[0]:
        collect_consts(a)

    if not init_consts:
        init_consts.add('c1')

    init_branch = {
        'pending': list(tableau[0]),
        'lits': [],
        'constants': list(init_consts),
        'universals': [],
        'forall_used': {}
    }
    branches.append(init_branch)

    # ============================================================
    #                     MAIN TABLEAU LOOP
    # ============================================================

    while branches:
        br = branches.pop()

        while br['pending']:
            f = br['pending'].pop()

            # literal
            if is_literal(f):
                if branch_closed(br['lits'] + [f]):
                    br = None
                    break
                br['lits'].append(f)
                continue

            k = f[0]

            # α
            if expand_alpha(br, f):
                continue

            # β
            if expand_beta(br, f, branches):
                br = None
                break

            # ¬
            if k == 'not':
                if expand_negation(br, f):
                    continue

            # γ
            if k == 'forall':
                r = expand_gamma(br, f)
                if r == 2:
                    return 2
                continue

            # δ
            if k == 'exists':
                r = expand_delta(br, f)
                if r == 2:
                    return 2
                continue

        if br is None:
            continue

        # check branch
        if branch_closed(br['lits']):
            continue
        if len(br['constants']) > MAX_CONSTANTS:
            return 2

        return 1

    return 0


# ============================================================
# DO NOT MODIFY BELOW THIS LINE  (UCL SKEL.)
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
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5, 8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line), rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
