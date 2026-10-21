/-ai
The empty set is not a neighbourhood of a separated sum.

A sum neighbourhood is the sum master, a left copy, or a right copy. The sum master contains the token none, and a left or right copy contains an element because its source neighbourhood is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- `∅` is never a sum-neighbourhood (every neighbourhood is non-empty). -/
theorem not_sum_mem_empty : ¬ (sum V₀ V₁ h₀ h₁).mem ∅ := by
  rintro (h | ⟨X, hX, h⟩ | ⟨Y, hY, h⟩)
  · exact absurd (h.symm ▸ none_mem_sumMaster) (Set.notMem_empty _)
  · obtain ⟨a, ha⟩ := inj₀_nonempty (h₀ X hX)
    exact absurd (h ▸ ha) (Set.notMem_empty _)
  · obtain ⟨b, hb⟩ := inj₁_nonempty (h₁ Y hY)
    exact absurd (h ▸ hb) (Set.notMem_empty _)

end DomainTheory.NeighbourhoodSystems.Exercise326
