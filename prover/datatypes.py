from __future__ import annotations
from typing import List, Dict
from dataclasses import dataclass
from sexpdata import Symbol

__all__ = [
    "Name", "Term", "Lit", "Var", "Symtree",
    "Derivation", "Sorry", "Proof",
    "InferenceRule", "State"
]

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

class Derivation: pass

@dataclass
class Proof(Derivation):
    edge          : Name
    children      : List[Derivation]
    substitutions : Dict[Name, Term]

@dataclass
class Sorry(Derivation):
    name : str

@dataclass
class InferenceRule:
    premises   : List[Term]
    conclusion : Term

@dataclass
class State:
    variables : List[Name]
    infix     : Dict[Symbol, int]
    context   : Dict[Name, State]