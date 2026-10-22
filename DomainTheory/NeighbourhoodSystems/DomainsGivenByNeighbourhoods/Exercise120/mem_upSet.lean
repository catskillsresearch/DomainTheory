/-ai
A set belongs to the up-set of a set if and only if it is a neighbourhood contained in that set.

The two sides are the defining condition of the up-set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_upSet {X Y : Set α} : Y ∈ V.upSet X ↔ V.mem Y ∧ Y ⊆ X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
