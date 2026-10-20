module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_funion
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion_empty_right
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Mutual subset is required for finset equality in this decidable instance. -/
theorem decidableEq_finset_false_of_ne (s t : Finset α) (h : ¬(s ⊆ t ∧ t ⊆ s)) (heq : s = t) :
    False := by
  subst heq
  exact h ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

end DomainTheory.InformationSystems.Constructive
