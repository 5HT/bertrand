from __future__ import annotations
from typing import List
from dataclasses import dataclass
from sexpdata import Symbol

Name = str

class Term: pass

@dataclass
class Lit(Term):
    name : Name

@dataclass
class Var(Term):
    name : Name

@dataclass
class Symtree(Term):
    children : List[Term]

def sexpr(τ):
    if isinstance(τ, Lit):
        return τ.name
    elif isinstance(τ, Var):
        return τ.name
    elif isinstance(τ, Symtree):
        return "(%s)" % " ".join(map(sexpr, τ.children))
Term.__str__ = sexpr

@dataclass
class ProofTree:
    edge          : Name
    children      : List[ProofTree]
    substitutions : Dict[Name, Term]

@dataclass
class InferenceRule:
    premises   : List[Term]
    conclusion : Term

@dataclass
class State:
    variables : List[Name]
    infix     : Dict[Symbol, int]
    context   : Dict[Name, Binding]