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

theorem decidableEq_finset.eq_of_subset (s t : Finset α) (h : s ⊆ t ∧ t ⊆ s) : s = t :=
  Finset.Subset.antisymm h.1 h.2

omit [DecidableEq α] in

theorem decidableEq_finset.false_of_ne (s t : Finset α) (h : ¬(s ⊆ t ∧ t ⊆ s)) (heq : s = t) :
    False := by
  subst heq
  exact h ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

def decidableEq_finset {α : Type*} [DecidableEq α] : DecidableEq (Finset α) :=
  fun s t =>
    if h : s ⊆ t ∧ t ⊆ s then
      isTrue (decidableEq_finset.eq_of_subset s t h)
    else
      isFalse (decidableEq_finset.false_of_ne s t h)

end DomainTheory.InformationSystems.Constructive
