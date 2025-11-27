MAX_CONSTANTS = 10

# Global symbol pools for clarity across parsing and tableau construction
PROPOSITION_SYMBOLS: tuple[str, ...] = tuple("abcdefghijklmnopqrstuvwxyz")
PREDICATE_SYMBOLS: tuple[str, ...] = tuple("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
VARIABLE_SYMBOLS: tuple[str, ...] = tuple("abcdefghijklmnopqrstuvwxyz")
CONSTANT_PREFIX: str = "c"


class ASTNode:
  def __init__(self, kind: str) -> None:
      self.kind = kind


class Prop(ASTNode):
  def __init__(self, name: str) -> None:
      super().__init__('prop')
      self.name = name


class Pred(ASTNode):
  def __init__(self, symbol: str, terms: tuple[str, ...]) -> None:
      super().__init__('pred')
      self.symbol = symbol
      self.terms = terms


class Not(ASTNode):
  def __init__(self, sub: 'AST') -> None:
      super().__init__('not')
      self.sub = sub


class And(ASTNode):
  def __init__(self, left: 'AST', right: 'AST') -> None:
      super().__init__('and')
      self.left = left
      self.right = right


class Or(ASTNode):
  def __init__(self, left: 'AST', right: 'AST') -> None:
      super().__init__('or')
      self.left = left
      self.right = right


class Imp(ASTNode):
  def __init__(self, left: 'AST', right: 'AST') -> None:
      super().__init__('imp')
      self.left = left
      self.right = right


class Forall(ASTNode):
  def __init__(self, var: str, body: 'AST') -> None:
      super().__init__('forall')
      self.var = var
      self.body = body


class Exists(ASTNode):
  def __init__(self, var: str, body: 'AST') -> None:
      super().__init__('exists')
      self.var = var
      self.body = body


AST = ASTNode


# Parse a formula, consult parseOutputs for return values.
def parse(fmla: str) -> int:

  global _binary_cache
  _binary_cache = getattr(parse, '_binary_cache', {})

  def is_prop_atom(s: str) -> bool:
      return len(s) == 1 and s in PROPOSITION_SYMBOLS

  def parse_predicate(s: str) -> AST | None:
      if len(s) < 4 or s[0] not in PREDICATE_SYMBOLS or s[1] != '(' or s[-1] != ')':
          return None
      body = s[2:-1]
      if body == '':
          return None
      for term in body.split(','):
          if not term.isalnum():
              return None
      return Pred(s[0], tuple(body.split(',')))

  def strip_parens(s: str) -> str:
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

  def find_main_connective(s: str) -> tuple[int | None, str | None]:
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

  def parse_formula(s: str) -> tuple[AST | None, int]:
      s = s.strip()
      if s == '':
          return None, 0

      # Proposition
      if is_prop_atom(s):
          return Prop(s), 6

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
              return Not(sub), 7
          else:
              return Not(sub), 2

      # Quantifiers
      if len(s) >= 3 and s[0] in ['A', 'E'] and s[1] in VARIABLE_SYMBOLS:
          quant = s[0]
          var = s[1]
          sub_fmla, sub_cls = parse_formula(s[2:])
          if not sub_fmla:
              return None, 0
          node = Forall(var, sub_fmla) if quant == 'A' else Exists(var, sub_fmla)
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
              node = Imp(left, right)
          elif conn == '&':
              node = And(left, right)
          else:
              node = Or(left, right)
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
def lhs(fmla: str) -> str:
  cache = getattr(parse, '_binary_cache', {})
  return cache.get(fmla, ('', '', ''))[0]

# Return the connective symbol of a binary connective formula
def con(fmla: str) -> str:
  cache = getattr(parse, '_binary_cache', {})
  return cache.get(fmla, ('', '', ''))[1]

# Return the RHS symbol of a binary connective formula
def rhs(fmla: str) -> str:
  cache = getattr(parse, '_binary_cache', {})
  return cache.get(fmla, ('', '', ''))[2]


# You may choose to represent a theory as a set or a list
def theory(fmla: str) -> list[AST]:#initialise a theory with a single formula in it
  ast = getattr(parse, '_ast_cache', {}).get(fmla)
  if not ast:
      parse(fmla)
      ast = getattr(parse, '_ast_cache', {}).get(fmla)
  return [ast] if ast else []

class Branch:
    def __init__(self, pending: list[AST], lits: list[AST], constants: list[str], universals: list[AST], forall_used: dict[str, set[str]]) -> None:
        self.pending = pending
        self.lits = lits
        self.constants = constants
        self.universals = universals
        self.forall_used = forall_used

    def copy_for_split(self, extra_formula: AST) -> "Branch":
        return Branch(
            pending=self.pending + [extra_formula],
            lits=list(self.lits),
            constants=list(self.constants),
            universals=list(self.universals),
            forall_used={k: set(v) for k, v in self.forall_used.items()},
        )


class ASTToolkit:
    def to_str(self, ast: AST) -> str:
        if ast.kind == 'prop':
            return ast.name  # type: ignore[attr-defined]
        if ast.kind == 'pred':
            return ast.symbol + '(' + ','.join(ast.terms) + ')'  # type: ignore[attr-defined]
        if ast.kind == 'not':
            return '~' + self.to_str(ast.sub)  # type: ignore[attr-defined]
        if ast.kind == 'and':
            return '(' + self.to_str(ast.left) + '&' + self.to_str(ast.right) + ')'
        if ast.kind == 'or':
            return '(' + self.to_str(ast.left) + '\\/' + self.to_str(ast.right) + ')'
        if ast.kind == 'imp':
            return '(' + self.to_str(ast.left) + '->' + self.to_str(ast.right) + ')'
        if ast.kind == 'forall':
            return 'A' + ast.var + self.to_str(ast.body)  # type: ignore[attr-defined]
        if ast.kind == 'exists':
            return 'E' + ast.var + self.to_str(ast.body)  # type: ignore[attr-defined]
        return ''

    def substitute(self, ast: AST, var: str, const: str) -> AST:
        kind = ast.kind
        if kind == 'pred':
            new_terms = tuple(const if t == var else t for t in ast.terms)  # type: ignore[attr-defined]
            return Pred(ast.symbol, new_terms)  # type: ignore[attr-defined]
        if kind == 'prop':
            return ast
        if kind == 'and':
            return And(self.substitute(ast.left, var, const), self.substitute(ast.right, var, const))  # type: ignore[attr-defined]
        if kind == 'or':
            return Or(self.substitute(ast.left, var, const), self.substitute(ast.right, var, const))  # type: ignore[attr-defined]
        if kind == 'imp':
            return Imp(self.substitute(ast.left, var, const), self.substitute(ast.right, var, const))  # type: ignore[attr-defined]
        if kind == 'not':
            return Not(self.substitute(ast.sub, var, const))  # type: ignore[attr-defined]
        if kind in ('forall', 'exists'):
            if ast.var == var:  # type: ignore[attr-defined]
                return ast
            if kind == 'forall':
                return Forall(ast.var, self.substitute(ast.body, var, const))  # type: ignore[attr-defined]
            return Exists(ast.var, self.substitute(ast.body, var, const))  # type: ignore[attr-defined]
        return ast

    def is_atom(self, ast: AST) -> bool:
        return ast.kind in ('prop', 'pred')

    def is_literal(self, ast: AST) -> bool:
        if ast.kind == 'not':
            return self.is_atom(ast.sub)  # type: ignore[attr-defined]
        return self.is_atom(ast)

    def complement(self, lit: AST) -> AST:
        if lit.kind == 'not':
            return lit.sub  # type: ignore[attr-defined]
        return Not(lit)

    def collect_constants(self, ast: AST, initial_constants: set[str]) -> None:
        kind = ast.kind
        if kind == 'pred':
            for term in ast.terms:  # type: ignore[attr-defined]
                if term.isupper() or term.startswith(CONSTANT_PREFIX):
                    initial_constants.add(term)
        elif kind in ('and', 'or', 'imp'):
            self.collect_constants(ast.left, initial_constants)  # type: ignore[attr-defined]
            self.collect_constants(ast.right, initial_constants)  # type: ignore[attr-defined]
        elif kind == 'not':
            self.collect_constants(ast.sub, initial_constants)  # type: ignore[attr-defined]
        elif kind in ('forall', 'exists'):
            self.collect_constants(ast.body, initial_constants)  # type: ignore[attr-defined]


class AlphaRule:
    def apply(self, branch: Branch, formula: AST) -> bool:
        if formula.kind == 'and':
            branch.pending.extend([formula.left, formula.right])  # type: ignore[attr-defined]
            return True
        if formula.kind == 'not':
            sub = formula.sub  # type: ignore[attr-defined]
            if sub.kind == 'not':
                branch.pending.append(sub.sub)  # type: ignore[attr-defined]
                return True
            if sub.kind == 'or':
                branch.pending.append(Not(sub.left))  # type: ignore[attr-defined]
                branch.pending.append(Not(sub.right))  # type: ignore[attr-defined]
                return True
            if sub.kind == 'imp':
                branch.pending.append(sub.left)  # type: ignore[attr-defined]
                branch.pending.append(Not(sub.right))  # type: ignore[attr-defined]
                return True
            if sub.kind == 'forall':
                branch.pending.append(Exists(sub.var, Not(sub.body)))  # type: ignore[attr-defined]
                return True
            if sub.kind == 'exists':
                branch.pending.append(Forall(sub.var, Not(sub.body)))  # type: ignore[attr-defined]
                return True
        return False


class BetaRule:
    def apply(self, branch: Branch, formula: AST) -> list[Branch] | None:
        if formula.kind == 'or':
            return [branch.copy_for_split(formula.left), branch.copy_for_split(formula.right)]  # type: ignore[attr-defined]
        if formula.kind == 'imp':
            left, right = formula.left, formula.right  # type: ignore[attr-defined]
            return [branch.copy_for_split(Not(left)), branch.copy_for_split(right)]
        if formula.kind == 'not' and formula.sub.kind == 'and':  # type: ignore[attr-defined]
            sub = formula.sub  # type: ignore[attr-defined]
            return [branch.copy_for_split(Not(sub.left)), branch.copy_for_split(Not(sub.right))]  # type: ignore[attr-defined]
        return None


class GammaRule:
    def __init__(self, toolkit: ASTToolkit) -> None:
        self.toolkit = toolkit

    def apply(self, branch: Branch, formula: AST) -> int | None:
        if formula.kind != 'forall':
            return None
        if formula not in branch.universals:
            branch.universals.append(formula)
        key = self.toolkit.to_str(formula)
        used = branch.forall_used.setdefault(key, set())
        if not branch.constants and not self._ensure_constant(branch, CONSTANT_PREFIX + '1'):
            return 2
        for const in list(branch.constants):
            if const not in used:
                branch.pending.append(self.toolkit.substitute(formula.body, formula.var, const))  # type: ignore[attr-defined]
                used.add(const)
        return 0

    def _ensure_constant(self, branch: Branch, const: str) -> bool:
        if const not in branch.constants:
            branch.constants.append(const)
        return True


class DeltaRule:
    def __init__(self, toolkit: ASTToolkit, max_constants: int) -> None:
        self.toolkit = toolkit
        self.max_constants = max_constants

    def apply(self, branch: Branch, formula: AST) -> int | None:
        if formula.kind != 'exists':
            return None
        new_const = CONSTANT_PREFIX + str(len(branch.constants) + 1)
        if not self._add_constant(branch, new_const):
            return 2
        branch.pending.append(self.toolkit.substitute(formula.body, formula.var, new_const))  # type: ignore[attr-defined]
        return 0

    def _add_constant(self, branch: Branch, const: str) -> bool:
        if const not in branch.constants:
            branch.constants.append(const)
        if len(branch.constants) > self.max_constants:
            return False
        for u in branch.universals:
            key = self.toolkit.to_str(u)
            used = branch.forall_used.setdefault(key, set())
            if const not in used:
                branch.pending.append(self.toolkit.substitute(u.body, u.var, const))  # type: ignore[attr-defined]
                used.add(const)
        return True

class TableauSolver:
    def __init__(self, max_constants: int = MAX_CONSTANTS) -> None:
        self.max_constants = max_constants
        self.toolkit = ASTToolkit()
        self.alpha_rule = AlphaRule()
        self.beta_rule = BetaRule()
        self.gamma_rule = GammaRule(self.toolkit)
        self.delta_rule = DeltaRule(self.toolkit, max_constants)

    def branch_closed(self, lits: list[AST]) -> bool:
        lit_set = set(self.toolkit.to_str(l) for l in lits)
        for lit in lits:
            if self.toolkit.to_str(self.toolkit.complement(lit)) in lit_set:
                return True
        return False

    def expand_branch(self, branch: Branch, branches: list[Branch]) -> int:
        while branch.pending:
            formula = branch.pending.pop()
            if self.toolkit.is_literal(formula):
                if self.branch_closed(branch.lits + [formula]):
                    return 0
                branch.lits.append(formula)
                continue

            if self.alpha_rule.apply(branch, formula):
                continue

            beta_branches = self.beta_rule.apply(branch, formula)
            if beta_branches is not None:
                branches.extend(beta_branches)
                return -1

            gamma_status = self.gamma_rule.apply(branch, formula)
            if gamma_status is not None:
                if gamma_status == 2:
                    return 2
                continue

            delta_status = self.delta_rule.apply(branch, formula)
            if delta_status is not None:
                if delta_status == 2:
                    return 2
                continue

        if self.branch_closed(branch.lits):
            return 0
        if len(branch.constants) > self.max_constants:
            return 2
        return 1

    def initial_branch(self, tableau: list[AST]) -> Branch:
        initial_constants: set[str] = set()
        for ast in tableau:
            self.toolkit.collect_constants(ast, initial_constants)
        if not initial_constants:
            initial_constants.add(CONSTANT_PREFIX + '1')
        return Branch(
            pending=list(tableau),
            lits=[],
            constants=list(initial_constants),
            universals=[],
            forall_used={},
        )

    def check(self, tableau: list[list[AST]]) -> int:
        branches: list[Branch] = [self.initial_branch(tableau[0])]
        while branches:
            branch = branches.pop()
            status = self.expand_branch(branch, branches)
            if status == 1:
                return 1
            if status == 2:
                return 2
        return 0


#check for satisfiability
def sat(tableau: list[list[AST]]) -> int:
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
  solver = TableauSolver()
  return solver.check(tableau)

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
