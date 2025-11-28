
MAX_CONSTANTS = 10



# Parse a formula, consult parseOutputs for return values.
def parse(fmla):

    global _binary_cache
    _binary_cache = getattr(parse, '_binary_cache', {})

    def is_prop_atom(s):
        return len(s) == 1 and s.islower()

    def parse_predicate(s):
        if len(s) < 4 or not s[0].isupper() or s[1] != '(' or s[-1] != ')':
            return None
        body = s[2:-1]
        if body == '':
            return None
        for term in body.split(','):
            if not term.isalnum():
                return None
        return ('pred', s[0], tuple(body.split(',')))

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

    def parse_formula(s):
        s = s.strip()
        if s == '':
            return None, 0

        # Proposition
        if is_prop_atom(s):
            return ('prop', s), 6

        # Predicate atom
        pred = parse_predicate(s)
        if pred:
            return pred, 1

        # Negation
        if s.startswith('~'):
            sub, cls = parse_formula(s[1:])
            if not sub:
                return None, 0
            if cls in [6, 7, 8]:
                return ('not', sub), 7
            else:
                return ('not', sub), 2

        # Quantifiers
        if len(s) >= 3 and s[0] in ['A', 'E'] and s[1].islower():
            quant = s[0]
            var = s[1]
            sub_fmla, sub_cls = parse_formula(s[2:])
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
            left, left_cls = parse_formula(left_s)
            right, right_cls = parse_formula(right_s)
            if not left or not right:
                return None, 0
            if conn == '->':
                node = ('imp', left, right)
            elif conn == '&':
                node = ('and', left, right)
            else:
                node = ('or', left, right)
            classification = 8 if left_cls in [6, 7, 8] and right_cls in [6, 7, 8] else 5
            _binary_cache[s] = (left_s, conn, right_s)
            return node, classification

        return None, 0

    ast, classification = parse_formula(fmla)
    parse._binary_cache = _binary_cache
    parse._ast_cache = getattr(parse, '_ast_cache', {})
    parse._ast_cache[fmla] = ast
    return classification

# Return the LHS of a binary connective formula
def lhs(fmla):
    cache = getattr(parse, '_binary_cache', {})
    return cache.get(fmla, ('', '', ''))[0]

# Return the connective symbol of a binary connective formula
def con(fmla):
    cache = getattr(parse, '_binary_cache', {})
    return cache.get(fmla, ('', '', ''))[1]

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    cache = getattr(parse, '_binary_cache', {})
    return cache.get(fmla, ('', '', ''))[2]


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    ast = getattr(parse, '_ast_cache', {}).get(fmla)
    if not ast:
        parse(fmla)
        ast = getattr(parse, '_ast_cache', {}).get(fmla)
    return [ast] if ast else []

#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    def to_str(ast):
        if ast[0] == 'prop':
            return ast[1]
        if ast[0] == 'pred':
            return ast[1] + '(' + ','.join(ast[2]) + ')'
        if ast[0] == 'not':
            return '~' + to_str(ast[1])
        if ast[0] == 'and':
            return '(' + to_str(ast[1]) + '&' + to_str(ast[2]) + ')'
        if ast[0] == 'or':
            return '(' + to_str(ast[1]) + '\\/' + to_str(ast[2]) + ')'
        if ast[0] == 'imp':
            return '(' + to_str(ast[1]) + '->' + to_str(ast[2]) + ')'
        if ast[0] == 'forall':
            return 'A' + ast[1] + to_str(ast[2])
        if ast[0] == 'exists':
            return 'E' + ast[1] + to_str(ast[2])

    def substitute(ast, var, const):
        kind = ast[0]
        if kind == 'pred':
            new_terms = tuple(const if t == var else t for t in ast[2])
            return ('pred', ast[1], new_terms)
        if kind == 'prop':
            return ast
        if kind in ('and', 'or', 'imp'):
            return (kind, substitute(ast[1], var, const), substitute(ast[2], var, const))
        if kind == 'not':
            return ('not', substitute(ast[1], var, const))
        if kind in ('forall', 'exists'):
            if ast[1] == var:
                return ast
            return (kind, ast[1], substitute(ast[2], var, const))
        return ast

    def is_literal(ast):
        if ast[0] == 'not':
            return is_atom(ast[1])
        return is_atom(ast)

    def is_atom(ast):
        return ast[0] in ('prop', 'pred')

    def complement(lit):
        if lit[0] == 'not':
            return lit[1]
        return ('not', lit)

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

    def branch_closed(lits):
        lit_set = set(to_str(l) for l in lits)
        for l in lits:
            comp = to_str(complement(l))
            if comp in lit_set:
                return True
        return False

    branches = []
    initial_constants = set()

    def collect_constants(ast):
        kind = ast[0]
        if kind == 'pred':
            for t in ast[2]:
                if t.isupper() or t.startswith('c'):
                    initial_constants.add(t)
        elif kind in ('and', 'or', 'imp'):
            collect_constants(ast[1])
            collect_constants(ast[2])
        elif kind == 'not':
            collect_constants(ast[1])
        elif kind in ('forall', 'exists'):
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

    while branches:
        br = branches.pop()
        while br['pending']:
            f = br['pending'].pop()
            if is_literal(f):
                if branch_closed(br['lits'] + [f]):
                    br = None
                    break
                br['lits'].append(f)
                continue

            kind = f[0]

            if kind == 'and':
                br['pending'].extend([f[1], f[2]])
                continue
            if kind == 'or':
                new_br1 = {
                    'pending': br['pending'] + [f[1]],
                    'lits': list(br['lits']),
                    'constants': list(br['constants']),
                    'universals': list(br['universals']),
                    'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
                }
                new_br2 = {
                    'pending': br['pending'] + [f[2]],
                    'lits': list(br['lits']),
                    'constants': list(br['constants']),
                    'universals': list(br['universals']),
                    'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
                }
                branches.append(new_br1)
                branches.append(new_br2)
                br = None
                break
            if kind == 'imp':
                left, right = f[1], f[2]
                new_br1 = {
                    'pending': br['pending'] + [('not', left)],
                    'lits': list(br['lits']),
                    'constants': list(br['constants']),
                    'universals': list(br['universals']),
                    'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
                }
                new_br2 = {
                    'pending': br['pending'] + [right],
                    'lits': list(br['lits']),
                    'constants': list(br['constants']),
                    'universals': list(br['universals']),
                    'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
                }
                branches.append(new_br1)
                branches.append(new_br2)
                br = None
                break
            if kind == 'not':
                sub = f[1]
                if sub[0] == 'not':
                    br['pending'].append(sub[1])
                    continue
                if sub[0] == 'and':
                    new_br1 = {
                        'pending': br['pending'] + [('not', sub[1])],
                        'lits': list(br['lits']),
                        'constants': list(br['constants']),
                        'universals': list(br['universals']),
                        'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
                    }
                    new_br2 = {
                        'pending': br['pending'] + [('not', sub[2])],
                        'lits': list(br['lits']),
                        'constants': list(br['constants']),
                        'universals': list(br['universals']),
                        'forall_used': {k: set(v) for k, v in br['forall_used'].items()}
                    }
                    branches.append(new_br1)
                    branches.append(new_br2)
                    br = None
                    break
                if sub[0] == 'or':
                    br['pending'].append(('not', sub[1]))
                    br['pending'].append(('not', sub[2]))
                    continue
                if sub[0] == 'imp':
                    br['pending'].append(sub[1])
                    br['pending'].append(('not', sub[2]))
                    continue
                if sub[0] == 'forall':
                    br['pending'].append(('exists', sub[1], ('not', sub[2])))
                    continue
                if sub[0] == 'exists':
                    br['pending'].append(('forall', sub[1], ('not', sub[2])))
                    continue
            if kind == 'forall':
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
                continue
            if kind == 'exists':
                new_const = 'c' + str(len(br['constants']) + 1)
                if not add_constant(br, new_const):
                    return 2
                br['pending'].append(substitute(f[2], f[1], new_const))
                continue

        if br is None:
            continue
        if branch_closed(br['lits']):
            continue
        if len(br['constants']) > MAX_CONSTANTS:
            return 2
        return 1

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