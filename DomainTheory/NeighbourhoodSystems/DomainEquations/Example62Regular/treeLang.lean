module

public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.pos_select

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

/-- **Scott's language of a tree.** `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` — the selectors that land on a
`+` node. Equivalently (by `pos_select`) the set of `σ` with `a σ = true`. A `Language (Fin n)` is
just a set of words over the alphabet, exactly Scott's "language". -/
def treeLang (a : Tree n) : Language (Fin n) := {σ | a σ = true}

end Example62Regular

end DomainTheory.NeighbourhoodSystems
