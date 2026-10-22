/-ai
If two finite sets are equal, then it is impossible that they fail to contain each other.

Substituting the equality, each set is a subset of itself, which contradicts the failure of mutual inclusion.
ai-/
module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_funion
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion_empty_right
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Mutual subset is required for finset equality in this decidable instance. -/
theorem decidableEq_finset_false_of_ne (s t : Finset α) (h : ¬(s ⊆ t ∧ t ⊆ s)) (heq : s = t) :
    False := by
  subst heq
  exact h ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

end DomainTheory.InformationSystems.Constructive
