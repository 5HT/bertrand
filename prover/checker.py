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
    elif isinstance(τ, Hole):
        return τ

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
    elif isinstance(φ, Lit) and isinstance(ψ, Lit):
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

def lookup(ctx : Dict[Name, InferenceRule], name : Name) -> InferenceRule:
    if name in ctx:
        return ctx[name]
    else:
        raise NotDefinedError(name)

def getbound(bound : List[Term], τ : Term) -> List[Name]:
    vars = []

    for formula in bound:
        substs = {}
        if unify(substs, formula, τ):
            for name, σ in substs.items():
                if not isinstance(σ, Var):
                    raise VerificationError("“%s” expected to be a variable" % σ)
            vars = maplist(lambda σ: σ.name, substs.values())
            break

    if isinstance(τ, Symtree):
        for child in τ.children:
            vars.extend(getbound(bound, child))
    return vars

def checksubst(bound : List[Term], substitutions : Dict[Name, Term], τ : Term):
    BV = getbound(bound, τ)
    for name, σ in substitutions.items():
        if name in BV and not isinstance(σ, Var):
            raise VerificationError(
                "cannot replace bound variable “{0}” with a constant “{1}”".format(
                    name, σ
                )
            )
        elif isinstance(σ, Var) and σ.name in BV:
            raise VerificationError(
                "cannot replace “{0}” with “{1}”, because “{1}” is bound".format(
                    name, σ.name
                )
            )

def sorry(tree : Sorry, τ : Term):
    print("%s: expected “%s”" % (tree.name, τ))

def infer(ctx : Dict[Name, InferenceRule], bound : List[Term],
          tree : Derivation) -> Term:
    statement = lookup(ctx, tree.edge)
    if len(tree.children) != len(statement.premises):
        raise VerificationError(
           "%s expects %d arguments, but got %d" % (
               tree.edge,
               len(statement.premises),
               len(tree.children)
           )
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