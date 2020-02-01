from functools import partial
from dataclasses import dataclass
from sys import argv

import os

import sexpdata
from sexpdata import Symbol, Bracket

from prover.datatypes import *
from prover.prelude import *
from prover.errors import *
from prover.checker import unify, multisubst, check
from prover.parser import symbol, term

def containsonly(ch, s):
    return all(c == ch for c in s)

def isseparator(expr):
    return isinstance(expr, Symbol) and \
           any(containsonly(ch, expr.value()) for ch in "─-")

def parseterm(curr, expr):
    return macroexpand(curr, term(curr, expr))

def macroexpand(curr, τ):
    for pattern, body in curr.defs:
        substs = {}
        if unify(substs, pattern, τ):
            τ = multisubst(substs, body)
            break

    if isinstance(τ, Symtree):
        τ = Symtree(maplist(partial(macroexpand, curr), τ.children))

    return τ

def postulate(curr, expr):
    premises = []
    while nonempty(expr):
        elem = expr.pop(0)
        if isseparator(elem):
            name = symbol(expr.pop(0))
            conclusion = parseterm(curr, expr.pop(0))

            if name in curr.context:
                print("Error: “%s” is already postulated" % name)
            else:
                curr.context[name] = InferenceRule(premises.copy(), conclusion)
            premises.clear()
        else:
            premises.append(parseterm(curr, elem))
    
    if nonempty(premises):
        raise SyntaxError("incomplete definition")

def keyvalue(curr, pair):
    ident, τ = pair
    return (symbol(ident), parseterm(curr, τ))

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
            return Proof(name, maplist(partial(tree, curr), judgments),
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
            premises.append(parseterm(curr, elem))
        else:
            name, conclusion = names.pop(), premises.pop()
            return name, conclusion, names, premises, tree(curr, elem)

def theorem(curr, expr):
    if not expr: return

    name, conclusion, names, premises, proof = preamble(curr, expr)
    τctx = curr.context.copy()
    τctx.update(
        (name, InferenceRule([], τ)) \
        for name, τ in zip(names, premises)
    )

    if name in curr.context:
            print("Error: theorem “%s” is already defined" % name)
    else:
        try:
            check(τctx, curr.bound, conclusion, proof)
            print("“%s” checked" % name)
            curr.context[name] = InferenceRule(premises, conclusion)
        except VerificationError as ex:
            print("“%s” has not been checked" % name)
            print("Error: %s" % ex.message)
    theorem(curr, expr)

def infix(curr, expr):
    ident, prec = expr
    assert isinstance(prec, int), "precedence must be an integer"
    name = symbol(ident)

    if name in curr.infix:
        print("Error: operator “%s” (%d) is already defined" % (
            name, curr.infix[name]
        ))
    else:
        curr.infix[name] = prec

def variables(curr, expr):
    curr.variables.extend(maplist(symbol, expr))

def bound(curr, expr):
    curr.bound.extend(maplist(partial(term, curr), expr))

def define(curr, expr):
    pattern, body = expr
    curr.defs.append(
        (term(curr, pattern), parseterm(curr, body))
    )

def include(curr, exprs):
    for expr in exprs:
        dopath(curr, symbol(expr))

forms = {
    "postulate": postulate,
    "theorem": theorem,
    "lemma": theorem,
    "infix": infix,
    "variables": variables,
    "bound": bound,
    "define": define,
    "include": include
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

def dofile(state, filename):
    print("Checking %s" % filename)
    with open(filename, 'r', encoding='utf-8') as fin:
        doexprs(state, fin.read())

def dopath(state, path):
    if not os.path.exists(path):
        print("Error: path %s does not exists" % path)
    elif os.path.isdir(path):
        print("Error: path %s is a directory" % path)
    else:
        dofile(state, path)

appname, *filenames = argv
state = State()
for filename in filenames: dopath(state, filename)