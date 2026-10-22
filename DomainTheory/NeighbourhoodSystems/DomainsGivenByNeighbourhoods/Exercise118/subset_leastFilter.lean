/-ai
Every member of a finitely consistent family belongs to the least filter containing the family.

A member is a neighbourhood. The one-term sequence repeating that member has intersection equal to the master intersected with the member, which is contained in the member.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.Basic

@[expose] public section


set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `C ⊆ leastFilter C`: every member of `C` is in the least filter. -/
theorem subset_leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) {W : Set α} (hW : W ∈ C) :
    (V.leastFilter C hCsub hC).mem W := by
  refine ⟨hCsub W hW, 1, (fun _ => W), (fun _ _ => hW), ?_⟩
  rw [interUpTo_succ, interUpTo_zero]
  exact Set.inter_subset_right

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
