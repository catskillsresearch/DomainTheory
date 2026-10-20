module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem retractLe_trans {a b c : Pomega}
    (hab : retractLe a b) (hbc : retractLe b c) :
    a = comp a c ∧ a = comp c a := by
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  constructor
  · -- `a ∘ c = (a ∘ b) ∘ c = a ∘ (b ∘ c) = a ∘ b = a`
    apply Eq.trans hab₁
    apply Eq.symm
    calc
      comp a c = graph (fun x => funOf a (funOf c x)) := rfl
      _ = graph (fun x => funOf (comp a b) (funOf c x)) := by simp [← hab₁]
      _ = graph (fun x => funOf a (funOf b (funOf c x))) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf (comp b c) x)) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf b x)) := by simp [← hbc₁]
      _ = comp a b := rfl
  · -- `c ∘ a = c ∘ (b ∘ a) = (c ∘ b) ∘ a = b ∘ a = a`
    apply Eq.trans hab₂
    apply Eq.symm
    calc
      comp c a = graph (fun x => funOf c (funOf a x)) := rfl
      _ = graph (fun x => funOf c (funOf (comp b a) x)) := by simp [← hab₂]
      _ = graph (fun x => funOf c (funOf b (funOf a x))) := by simp [comp_app]
      _ = graph (fun x => funOf (comp c b) (funOf a x)) := by simp [comp_app]
      _ = graph (fun x => funOf b (funOf a x)) := by
        -- `c ∘ b = b` is `hbc₂`? `retractLe b c` is `b = b ∘ c` and `b = c ∘ b`
        simp [← hbc₂]
      _ = comp b a := rfl

end DomainTheory.DataTypesAsLattices
