/-ai
A token lies in the i-th fiber of a set of pairs exactly when the pair of i with that token lies in the set.

The identity is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

@[simp] theorem mem_fiber {W : Set (ℕ × α)} {i : ℕ} {a : α} : a ∈ fiber W i ↔ (i, a) ∈ W := Iff.rfl

end DomainTheory.NeighbourhoodSystems
