
MAX_CONSTANTS = 10



# Parse a formula, consult parseOutputs for return values.
def parse(fmla: str) -> int:
    if parse_prop(fmla):
        return parse_prop(fmla)
    return parse_fol(fmla)

# Return the LHS of a binary connective formula
def lhs(fmla: str) -> str:
    parts = split_binary(fmla)
    if parts:
        return parts[0]
    return ''

# Return the connective symbol of a binary connective formula
def con(fmla: str) -> str:
    parts = split_binary(fmla)
    if parts:
        return parts[1]
    return ''

# Return the RHS symbol of a binary connective formula
def rhs(fmla: str) -> str:
    parts = split_binary(fmla)
    if parts:
        return parts[2]
    return ''


# You may choose to represent a theory as a set or a list
def theory(fmla: str) -> dict[str,list[str]]:#initialise a theory with a single formula in it
    return {'fmla':[fmla],'const':set(),'applied':{}}

#check for satisfiability
def sat(tableau: list[str]) -> int:
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    while tableau:
        branch = tableau.pop()

        if len(branch['const']) > MAX_CONSTANTS:
            return 2

        closed, literals = check_closed(branch['fmla'])
        if closed:
            continue

        target = next((f for f in branch['fmla'] if needs_expansion(f, branch)), None)
        if target is None:
            return 1

        new_branches = expand_formula(target, branch)
        tableau.extend(new_branches)

    return 0


# --------------------------------------------------
# Helper functions
# --------------------------------------------------

def is_prop_atom(fmla: str) -> bool:
    return fmla in ['p','q','r','s']


def is_pred_atom(fmla: str) -> bool:
    if len(fmla) < 4:
        return False
    if not fmla[0].isupper() or fmla[1] != '(' or fmla[-1] != ')':
        return False

    args = fmla[2:-1]
    if not args:
        return False

    parts = args.split(',')
    return all(len(p) == 1 and p.islower() for p in parts)


def split_binary(fmla: str) -> tuple[str,str,str]:
    if len(fmla) < 5 or fmla[0] != '(' or fmla[-1] != ')':
        return None
    level = 0
    i = 0
    while i < len(fmla):
        ch = fmla[i]
        if ch == '(':
            level += 1
        elif ch == ')':
            level -= 1
        elif level == 1:
            if fmla.startswith('->', i):
                return (fmla[1:i], '->', fmla[i+2:-1])
            if fmla.startswith('\\/', i):
                return (fmla[1:i], '\\/', fmla[i+2:-1])
            if ch == '&':
                return (fmla[1:i], '&', fmla[i+1:-1])
        i += 1
    return None


def parse_prop(fmla: str) -> int:
    if is_prop_atom(fmla):
        return 6
    if fmla.startswith('~'):
        inner = parse_prop(fmla[1:])
        if inner:
            return 7
        return 0
    parts = split_binary(fmla)
    if parts:
        left,right = parts[0],parts[2]
        if parse_prop(left) and parse_prop(right):
            return 8
    return 0


def parse_fol(fmla: str) -> int:
    if is_pred_atom(fmla):
        return 1
    if fmla.startswith('~'):
        inner = parse_fol(fmla[1:])
        if inner:
            return 2
        return 0
    if len(fmla) >= 2 and fmla[0] in ['A','E'] and fmla[1].islower():
        rest = fmla[2:]
        if not rest:
            return 0
        if parse_fol(rest):
            return 3 if fmla[0] == 'A' else 4
    parts = split_binary(fmla)
    if parts:
        left,right = parts[0],parts[2]
        if parse_fol(left) and parse_fol(right):
            return 5
    return 0


def is_literal(fmla: str) -> bool:
    if parse_prop(fmla) == 6 or parse_fol(fmla) == 1:
        return True
    if fmla.startswith('~'):
        inner = fmla[1:]
        return parse_prop(inner) == 6 or parse_fol(inner) == 1
    return False


def check_closed(formulas: list[str]) -> tuple[bool, set[str]]:
    literals = set()
    for f in formulas:
        if is_literal(f):
            literals.add(f)
    for lit in literals:
        if lit.startswith('~') and lit[1:] in literals:
            return True, literals
        if ('~'+lit) in literals:
            return True, literals
    return False, literals


def needs_expansion(fmla: str, branch: dict[str,list[str]]) -> bool:
    if is_literal(fmla):
        return False
    parsed = parse_fol(fmla)
    if parsed == 3:  # universal
        processed = branch.get('applied',{}).get(fmla,set())
        return len(branch['const']) == 0 or len(processed) < len(branch['const'])
    if fmla.startswith('~'):
        inner = fmla[1:]
        if parse_fol(inner) == 4:  # ~Ex phi behaves like universal
            processed = branch.get('applied',{}).get(fmla,set())
            return len(branch['const']) == 0 or len(processed) < len(branch['const'])
    return True


def substitute_var(fmla: str, var: str, const: str) -> str:
    return fmla.replace(var, const)


def new_constant(existing: set) -> str:
    for ch in 'abcdefghijklmnopqrstuvwxyz':
        if ch not in existing:
            return ch
    return 'c%s' % (len(existing)+1)


def expand_formula(fmla: str, branch: dict[str,list[str]]) -> list:
    formulas = [f for f in branch['fmla'] if f != fmla]
    consts = set(branch['const'])
    applied = {k:set(v) for k,v in branch.get('applied',{}).items()}

    if parse_prop(fmla):
        return expand_prop(fmla, formulas, consts, applied)
    return expand_fol(fmla, formulas, consts, applied)


def expand_prop(fmla: str, formulas: list[str], consts: set, applied: dict[str, list[str]]) -> list[str]:
    res = []
    if fmla.startswith('~'):
        inner = fmla[1:]
        parsed_inner = parse_prop(inner)
        if parsed_inner == 7:  # double negation
            res.append({'fmla':formulas+[inner[1:]], 'const':consts,'applied':applied})
        elif parsed_inner == 8:
            l,c,r = split_binary(inner)
            if c == '&':
                res.append({'fmla':formulas+['~'+l], 'const':consts,'applied':applied})
                res.append({'fmla':formulas+['~'+r], 'const':consts,'applied':applied})
            elif c == '\\/':
                res.append({'fmla':formulas+['~'+l, '~'+r], 'const':consts,'applied':applied})
            elif c == '->':
                res.append({'fmla':formulas+[l,'~'+r], 'const':consts,'applied':applied})
        elif parsed_inner == 6:
            res.append({'fmla':formulas+[fmla], 'const':consts,'applied':applied})
    else:
        parsed = parse_prop(fmla)
        if parsed == 8:
            l,c,r = split_binary(fmla)
            if c == '&':
                res.append({'fmla':formulas+[l,r], 'const':consts,'applied':applied})
            elif c == '\\/':
                res.append({'fmla':formulas+[l], 'const':consts,'applied':applied})
                res.append({'fmla':formulas+[r], 'const':consts,'applied':applied})
            elif c == '->':
                res.append({'fmla':formulas+['~'+l], 'const':consts,'applied':applied})
                res.append({'fmla':formulas+[r], 'const':consts,'applied':applied})
        elif parsed == 6:
            res.append({'fmla':formulas+[fmla], 'const':consts,'applied':applied})
    return res


def expand_fol(fmla: str, formulas: list[str], consts: set, applied: dict[str, list[str]]) -> list[str]:
    res = []
    if fmla.startswith('~'):
        inner = fmla[1:]
        parsed_inner = parse_fol(inner)
        if parsed_inner == 2:  # double negation
            res.append({'fmla':formulas+[inner[1:]], 'const':consts,'applied':applied})
        elif parsed_inner == 5:
            l,c,r = split_binary(inner)
            if c == '&':
                res.append({'fmla':formulas+['~'+l], 'const':consts,'applied':applied})
                res.append({'fmla':formulas+['~'+r], 'const':consts,'applied':applied})
            elif c == '\\/':
                res.append({'fmla':formulas+['~'+l,'~'+r], 'const':consts,'applied':applied})
            elif c == '->':
                res.append({'fmla':formulas+[l,'~'+r], 'const':consts,'applied':applied})
        elif parsed_inner == 3:  # ~Ax phi -> Ex ~phi
            var = inner[1]
            inner_f = inner[2:]
            const = new_constant(consts)
            consts.add(const)
            inst = substitute_var(inner_f, var, const)
            res.append({'fmla':formulas+['~'+inst], 'const':consts,'applied':applied})
        elif parsed_inner == 4:  # ~Ex phi -> Ax ~phi
            var = inner[1]
            inner_f = inner[2:]
            if not consts:
                const = new_constant(consts)
                consts.add(const)
            processed = applied.get(fmla,set())
            new_consts = [c for c in consts if c not in processed]
            branches = []
            for cst in new_consts:
                inst = substitute_var(inner_f, var, cst)
                branches.append('~'+inst)
            processed.update(consts)
            applied[fmla]=processed
            res.append({'fmla':formulas+branches+[fmla], 'const':consts,'applied':applied})
        elif parsed_inner == 1:
            res.append({'fmla':formulas+[fmla], 'const':consts,'applied':applied})
    else:
        parsed = parse_fol(fmla)
        if parsed == 5:
            l,c,r = split_binary(fmla)
            if c == '&':
                res.append({'fmla':formulas+[l,r], 'const':consts,'applied':applied})
            elif c == '\\/':
                res.append({'fmla':formulas+[l], 'const':consts,'applied':applied})
                res.append({'fmla':formulas+[r], 'const':consts,'applied':applied})
            elif c == '->':
                res.append({'fmla':formulas+['~'+l], 'const':consts,'applied':applied})
                res.append({'fmla':formulas+[r], 'const':consts,'applied':applied})
        elif parsed == 3:  # Ax phi
            var = fmla[1]
            inner = fmla[2:]
            if not consts:
                const = new_constant(consts)
                consts.add(const)
            processed = applied.get(fmla,set())
            new_consts = [c for c in consts if c not in processed]
            instantiations = [substitute_var(inner, var, c) for c in new_consts]
            processed.update(consts)
            applied[fmla]=processed
            res.append({'fmla':formulas+instantiations+[fmla], 'const':consts,'applied':applied})
        elif parsed == 4:  # Ex phi
            var = fmla[1]
            inner = fmla[2:]
            const = new_constant(consts)
            consts.add(const)
            inst = substitute_var(inner, var, const)
            res.append({'fmla':formulas+[inst], 'const':consts,'applied':applied})
        elif parsed == 1:
            res.append({'fmla':formulas+[fmla], 'const':consts,'applied':applied})
    return res

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