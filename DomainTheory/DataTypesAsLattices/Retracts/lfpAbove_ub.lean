module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem lfpAbove_ub {f : Pomega → Pomega} {A : Set Pomega} :
    ∀ x ∈ A, x ⊆ lfpAbove f (⋃₀ A) := by
  intro x hx k hk
  exact Set.mem_iUnion.mpr ⟨0, Set.subset_sUnion_of_mem hx hk⟩

end DomainTheory.DataTypesAsLattices
