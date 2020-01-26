from prover.datatypes import *
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
    elif isinstance(τ, Symtree):
        return Symtree(maplist(partial(subst, name, μ), τ.children))

def dictsubst(substitutions : Dict[Name, Term], τ : Term) -> Term:
    salt = gensym()
    for name, _ in substitutions.items():
        τ = subst(name, Var(name + salt), τ)

    for name, μ in substitutions.items():
        τ = subst(name + salt, μ, τ)

    for name, _ in substitutions.items():
        τ = subst(name + salt, Var(name), τ)
    return τ

def unify(φ : Term, ψ : Term):
    if (isinstance(φ, Var) and isinstance(ψ, Var)) or \
       (isinstance(φ, Lit) and isinstance(ψ, Lit)):
        if φ.name != ψ.name:
            raise UnificationError(φ, ψ)
    elif isinstance(φ, Symtree) and isinstance(ψ, Symtree):
        for δφ, δψ in zip(φ.children, ψ.children):
            unify(δφ, δψ)
    else:
        raise UnificationError(φ, ψ)

def lookup(ctx : Dict[Name, InferenceRule], name : Name) -> Term:
    if name in ctx:
        return ctx[name]
    else:
        raise NotDefinedError(name)

def sorry(tree : Sorry, τ : Term):
    print("%s: expected “%s”" % (tree.name, τ))

def infer(ctx : Dict[Name, InferenceRule], tree : Derivation) -> Term:
    statement = lookup(ctx, tree.edge)
    assert len(tree.children) == len(statement.premises), \
           "expected %d arguments, but got %d" % (
               len(statement.premises),
               len(tree.children)
           )

    for premise, child in zip(statement.premises, tree.children):
        expected = dictsubst(tree.substitutions, premise)
        if isinstance(child, Sorry):
            sorry(child, expected)
        elif isinstance(child, Proof):
            τ = infer(ctx, child)
            unify(expected, τ)

    return dictsubst(tree.substitutions, statement.conclusion)

def check(ctx : Dict[Name, InferenceRule], τ : Term, tree : Derivation):
    # top-level sorry
    if isinstance(tree, Sorry):
        sorry(tree, τ)
    else:
        π = infer(ctx, tree)
        unify(π, τ)