/-ai
A set lies in the union of the down-sets of the neighbourhoods in a list if and only if it lies in the down-set of some neighbourhood in that list.

Rewrite indexed-union membership so that the list membership of the witness is explicit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- Membership in a finite union of down-sets: `z ∈ ⋃_{X∈L} ↓X ↔ ∃ X ∈ L, z ∈ ↓X`. -/
theorem mem_PDunion {L : List (Set α)} {z : Set α} :
    z ∈ (⋃ X ∈ L, V.upSet X) ↔ ∃ X ∈ L, z ∈ V.upSet X := by
  simp only [Set.mem_iUnion, exists_prop]

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
