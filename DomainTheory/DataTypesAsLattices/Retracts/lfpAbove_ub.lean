/-ai
Every member of a family A is contained in the least upper bound of the iterates of f above the union of A.

An element of such a member lies in the zero iterate, because that member is one of the sets being united.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem lfpAbove_ub {f : Pomega → Pomega} {A : Set Pomega} :
    ∀ x ∈ A, x ⊆ lfpAbove f (⋃₀ A) := by
  intro x hx k hk
  exact Set.mem_iUnion.mpr ⟨0, Set.subset_sUnion_of_mem hx hk⟩

end DomainTheory.DataTypesAsLattices
