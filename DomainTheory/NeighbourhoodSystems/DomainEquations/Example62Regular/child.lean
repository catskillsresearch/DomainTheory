/-ai
The i-th immediate subtree of a total tree is the subtree selected by the one-letter word consisting of i.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

/-- The `i`-th immediate subtree `aᵢ = a i` (Scott's children of the root node). -/
def child (a : Tree n) (i : Fin n) : Tree n := select a [i]

end Example62Regular

end DomainTheory.NeighbourhoodSystems
