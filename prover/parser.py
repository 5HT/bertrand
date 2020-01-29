import sexpdata
from sexpdata import Symbol, Bracket
from functools import partial

from prover.prelude   import *
from prover.datatypes import *
from prover.errors    import *

def symbol(expr):
    if isinstance(expr, Symbol):
        return expr.value()
    elif isinstance(expr, int):
        return str(expr)

    raise SyntaxError("expected symbol at “%s”" % expr)

def operator(out, stack):
    f, y, x = Lit(stack.pop()), out.pop(), out.pop()
    out.append(Symtree([x, f, y]))

def shuntingyard(curr, exprs):
    out, stack = [], []

    for expr in exprs:
        if isinstance(expr, Symbol) and \
           symbol(expr) in curr.infix:
            lit = symbol(expr)
            while nonempty(stack) and \
                  curr.infix[first(stack)] > curr.infix[lit]:
                operator(out, stack)
            stack.append(lit)
        else:
            out.append(term(curr, expr))
    while nonempty(stack):
        operator(out, stack)

    if is_singleton(out):
        return first(out)
    else:
        raise ValueError("infix parsing failed")

def term(curr, expr):
    if isinstance(expr, list):
        if len(expr) == 0:
            raise ValueError("empty expression")

        if isinstance(first(expr), Symbol) and \
           first(expr).value() == "#":
            expr.pop(0)
            return shuntingyard(curr, expr)
        else:
            return Symtree(maplist(partial(term, curr), expr))
    elif isinstance(expr, Symbol):
        string = expr.value()
        if string == "_":
            return Hole()
        elif string in curr.variables:
            return Var(string)
        else:
            return Lit(string)
    elif isinstance(expr, int):
        return Lit(str(expr))
    else:
        raise InvalidTermError(expr)