/-ai
The union of the down-sets of the sets in the empty list is empty.

Membership in that union would require a member of the empty list, so the two sides have the same elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite union `⋃_{X ∈ []} ↓X` is empty. -/
theorem upSetUnion_nil : (⋃ X ∈ ([] : List (Set α)), V.upSet X) = ∅ := by
  ext z
  rw [V.mem_PDunion]
  simp only [List.not_mem_nil, false_and, exists_false, Set.mem_empty_iff_false]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
