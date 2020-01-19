from __future__ import annotations
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
class App(Term):
    edge     : Term
    children : List[Term]

def sexpr(τ):
    if isinstance(τ, Lit):
        return τ.name
    elif isinstance(τ, Var):
        return τ.name
    elif isinstance(τ, App):
        return "(%s %s)" % (sexpr(τ.edge),
                            " ".join(map(sexpr, τ.children)))
Term.__str__ = sexpr

@dataclass
class Tree:
    edge          : Name
    children      : List[Tree]
    substitutions : Dict[Name, Term]

@dataclass
class Binding:
    hypotheses : List[Term]
    thesis     : Term

@dataclass
class State:
    variables : List[Name]
    infix     : Dict[Symbol, int]
    context   : Dict[Name, Binding]