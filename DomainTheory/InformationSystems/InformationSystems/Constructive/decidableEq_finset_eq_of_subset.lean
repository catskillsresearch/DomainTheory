/-ai
Finite sets that contain each other are equal.

Antisymmetry of inclusion is applied to the two inclusions.
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
/-- If mutual subset holds, the finsets are equal. -/
theorem decidableEq_finset_eq_of_subset (s t : Finset α) (h : s ⊆ t ∧ t ⊆ s) : s = t :=
  Finset.Subset.antisymm h.1 h.2

end DomainTheory.InformationSystems.Constructive
