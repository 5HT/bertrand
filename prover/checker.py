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

def multisubst(substitutions : Dict[Name, Term], τ : Term) -> Term:
    salt = gensym()
    for name, _ in substitutions.items():
        τ = subst(name, Var(name + salt), τ)

    for name, μ in substitutions.items():
        τ = subst(name + salt, μ, τ)

    for name, _ in substitutions.items():
        τ = subst(name + salt, Var(name), τ)
    return τ

def prune(substs : Dict[Name, Term], τ : Term):
    if isinstance(τ, Var):
        if τ.name in substs:
            return substs[τ.name]
        else:
            return τ
    else:
        return τ

def unify(substs : Dict[Name, Term], α : Term, β : Term) -> bool:
    φ, ψ = prune(substs, α), prune(substs, β)
    if isinstance(φ, Var):
        substs[φ.name] = ψ
        return True
    if isinstance(φ, Lit) and isinstance(ψ, Lit):
        return φ.name == ψ.name
    elif isinstance(φ, Symtree) and isinstance(ψ, Symtree):
        if len(φ.children) != len(ψ.children):
            return False
        for δφ, δψ in zip(φ.children, ψ.children):
            if not unify(substs, δφ, δψ):
                return False
        return True
    elif isinstance(φ, Hole):
        return True
    else:
        return False

def occurs(τ : Term, name : Name):
    if isinstance(τ, Var):
        return τ.name == name
    elif isinstance(τ, Lit):
        return False
    elif isinstance(τ, Symtree):
        for σ in τ.children:
            if occurs(σ, name):
                return True
        return False
    else:
        return False

def even(φ : Term, ψ : Term):
    if φ != ψ:
        raise UnificationError(φ, ψ)

def lookup(ctx : Dict[Name, InferenceRule], name : Name) -> Term:
    if name in ctx:
        return ctx[name]
    else:
        raise NotDefinedError(name)

def getbound(bound : List[Term], τ : Term) -> List[Name]:
    for formula in bound:
        substs = {}
        if unify(substs, formula, τ):
            assert all(map(lambda σ: isinstance(σ, Var), substs.values())), \
                   "cannot substitute variable binder with term"
            vars = maplist(lambda σ: σ.name, substs.values())
            if isinstance(τ, Symtree):
                for child in τ.children:
                    vars.extend(getbound(bound, child))
            return vars
    return []

def checksubst(bound : List[Term], substitutions : Dict[Name, Term], τ : Term):
    BV = getbound(bound, τ)
    for name, σ in substitutions.items():
        if isinstance(σ, Var) and σ.name in BV:
            raise VerificationError(
                "cannot replace “%s” with “%s”, because it is bound" % (
                    name, σ.name
                )
            )

def sorry(tree : Sorry, τ : Term):
    print("%s: expected “%s”" % (tree.name, τ))

def infer(ctx : Dict[Name, InferenceRule], bound : List[Term],
          tree : Derivation) -> Term:
    statement = lookup(ctx, tree.edge)
    assert len(tree.children) == len(statement.premises), \
           "expected %d arguments, but got %d" % (
               len(statement.premises),
               len(tree.children)
           )

    for premise, child in zip(statement.premises, tree.children):
        checksubst(bound, tree.substitutions, premise)
        expected = multisubst(tree.substitutions, premise)
        if isinstance(child, Sorry):
            sorry(child, expected)
        elif isinstance(child, Proof):
            τ = infer(ctx, bound, child)
            even(expected, τ)

    checksubst(bound, tree.substitutions, statement.conclusion)
    return multisubst(tree.substitutions, statement.conclusion)

def check(ctx : Dict[Name, InferenceRule], bound : List[Term],
          τ : Term, tree : Derivation):
    # top-level sorry
    if isinstance(tree, Sorry):
        sorry(tree, τ)
    else:
        π = infer(ctx, bound, tree)
        even(π, τ)