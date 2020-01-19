from prover.datatypes import Name, Term, Lit, Var, App, Tree, Binding
from prover.prelude import *
from prover.errors import *

from functools import partial
from typing import List, Dict

def subst(name : Name, μ : Term, τ : Term) -> Term:
    if isinstance(τ, Lit):
        return τ
    elif isinstance(τ, Var):
        if τ.name == name:
            return μ
        else:
            return τ
    elif isinstance(τ, App):
        return App(subst(name, μ, τ.edge),
                   maplist(partial(subst, name, μ), τ.children))

def dictsubst(substitutions : Dict[Name, Term], τ : Term) -> Term:
    salt = gensym()
    for name, _ in substitutions.items():
        τ = subst(name, Var(name + salt), τ)

    for name, μ in substitutions.items():
        τ = subst(name + salt, μ, τ)

    for name, _ in substitutions.items():
        τ = subst(name + salt, Var(name), τ)
    return τ

def prune(s : Dict[Name, Term], τ : Term) -> Term:
    if isinstance(τ, Var):
        return s.get(τ.name, τ)
    elif isinstance(τ, App):
        return App(prune(s, τ.edge),
                   maplist(partial(prune, s), τ.children))
    else:
        return τ

def unify(s : Dict[Name, Term], α : Term, β : Term):
    φ, ψ = prune(s, α), prune(s, β)
    if isinstance(φ, Var) and isinstance(ψ, Var):
        s[φ.name] = ψ
    elif isinstance(φ, Lit) and isinstance(ψ, Lit):
        if φ.name != ψ.name:
            raise UnificationError(φ, ψ)
    elif isinstance(φ, App) and isinstance(ψ, App):
        unify(s, φ.edge, ψ.edge)
        for δφ, δψ in zip(φ.children, ψ.children):
            unify(s, δφ, δψ)
    else:
        raise UnificationError(φ, ψ)

def lookup(ctx : Dict[Name, Binding], name : Name) -> Term:
    if name in ctx:
        return ctx[name]
    else:
        raise NotDefinedError(name)

def infer(ctx : Dict[Name, Binding], tree : Tree) -> Term:
    statement = lookup(ctx, tree.edge)
    assert len(tree.children) == len(statement.hypotheses), \
           "invalid statement application"
    substitutions = {}
    for expected, subtree in zip(statement.hypotheses, tree.children):
        τ = infer(ctx, subtree)
        unify(substitutions, dictsubst(tree.substitutions, expected), τ)

    return dictsubst(tree.substitutions, statement.thesis)

def check(ctx : Dict[Name, Binding], τ : Term, tree : Tree):
    π = infer(ctx, tree)
    unify({}, π, τ)