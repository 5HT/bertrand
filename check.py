from functools import partial
from sys import argv

import sexpdata
from sexpdata import Symbol, Bracket

from prover.datatypes import *
from prover.prelude import *
from prover.errors import *
from prover.checker import check
from prover.parser import symbol, term

def containsonly(ch, s):
    return all(c == ch for c in s)

def isseparator(expr):
    return isinstance(expr, Symbol) and \
           any(containsonly(ch, expr.value()) for ch in "─-")

def postulate(curr, expr):
    premises = []
    while nonempty(expr):
        elem = expr.pop(0)
        if isseparator(elem):
            name = symbol(expr.pop(0))
            conclusion = term(curr, expr.pop(0))
            curr.context[name] = InferenceRule(premises.copy(), conclusion)

            premises.clear()
        else:
            premises.append(term(curr, elem))
    
    if nonempty(premises):
        raise SyntaxError("incomplete definition")

def keyvalue(curr, pair):
    ident, τ = pair
    return (symbol(ident), term(curr, τ))

def genenv(curr, lst):
    return map(partial(keyvalue, curr),
               evensplit(lst))

def tree(curr, expr):
    if isinstance(expr, list):
        ident, *judgments, rest = expr
        name = symbol(ident)

        if name == "sorry":
            return Sorry(symbol(rest))
        else:
            return Proof(name,
                         maplist(partial(tree, curr), judgments),
                         dict(genenv(curr, rest)))
    elif isinstance(expr, Symbol):
        return Proof(symbol(expr), [], {})
    elif isinstance(expr, int):
        return Proof(str(expr), [], {})
    else:
        raise SyntaxError("“%s” is not proof tree" % str(expr))

def preamble(curr, expr):
    names, premises = [], []
    expected = 0

    while True:
        elem = expr.pop(0)
        if isseparator(elem):
            expected += 1
            names.append(symbol(expr.pop(0)))
        elif expected != 0:
            expected -= 1
            premises.append(term(curr, elem))
        else:
            name, conclusion = names.pop(), premises.pop()
            return name, conclusion, names, premises, tree(curr, elem)

def theorem(curr, expr):
    if not expr:
        return

    name, conclusion, names, premises, proof = preamble(curr, expr)
    τctx = curr.context.copy()
    τctx.update(
        (name, InferenceRule([], τ)) \
        for name, τ in zip(names, premises)
    )

    try:
        check(τctx, curr.bound, conclusion, proof)
        print("“%s” checked" % name)
        curr.context[name] = InferenceRule(premises, conclusion)
    except VerificationError as ex:
        print("“%s” has not been checked" % name)
        print("Error: %s" % ex.message)

    theorem(curr, expr)

def infix(curr, expr):
    name, prec = expr
    assert isinstance(prec, int), "precedence must be an integer"
    curr.infix[symbol(name)] = prec

def variables(curr, expr):
    curr.variables.extend(maplist(symbol, expr))

def bound(curr, expr):
    curr.bound.extend(maplist(partial(term, curr), expr))

forms = {
    "postulate": postulate,
    "theorem": theorem,
    "lemma": theorem,
    "infix": infix,
    "variables": variables,
    "bound": bound
}
def evaluate(curr, expr):
    head, *tail = expr
    form = symbol(head)

    assert form in forms, "unknown form “%s”" % form
    forms[form](curr, tail)

def doexprs(curr, string):
    curr.variables = []
    for expr in sexpdata.parse(string):
        evaluate(curr, expr)

appname, *filenames = argv
curr = State()
for filename in filenames:
    print("Checking %s" % filename)
    with open(filename, 'r', encoding='utf-8') as fin:
        doexprs(curr, fin.read())