module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- The `i`-th *fiber* of a set `W ⊆ ℕ × α`: the tokens appearing in copy `i`. -/
def fiber (W : Set (ℕ × α)) (i : ℕ) : Set α := {a | (i, a) ∈ W}

end DomainTheory.NeighbourhoodSystems
