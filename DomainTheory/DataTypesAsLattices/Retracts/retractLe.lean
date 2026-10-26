module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.Retract

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §4, Definition.** `a ⊑ b` iff `a = a ∘ b = b ∘ a`. -/
def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a

namespace retractLe

theorem refl {a : Pomega} (ha : Retract a) : retractLe a a :=
  ⟨ha.out, ha.out⟩

theorem trans {a b c : Pomega}
    (hab : retractLe a b) (hbc : retractLe b c) :
    retractLe a c := by
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  constructor
  · apply Eq.trans hab₁
    apply Eq.symm
    calc
      comp a c = graph (fun x => funOf a (funOf c x)) := rfl
      _ = graph (fun x => funOf (comp a b) (funOf c x)) := by simp [← hab₁]
      _ = graph (fun x => funOf a (funOf b (funOf c x))) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf (comp b c) x)) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf b x)) := by simp [← hbc₁]
      _ = comp a b := rfl
  · apply Eq.trans hab₂
    apply Eq.symm
    calc
      comp c a = graph (fun x => funOf c (funOf a x)) := rfl
      _ = graph (fun x => funOf c (funOf (comp b a) x)) := by simp [← hab₂]
      _ = graph (fun x => funOf c (funOf b (funOf a x))) := by simp [comp_app]
      _ = graph (fun x => funOf (comp c b) (funOf a x)) := by simp [comp_app]
      _ = graph (fun x => funOf b (funOf a x)) := by simp [← hbc₂]
      _ = comp b a := rfl

end retractLe

end DomainTheory.DataTypesAsLattices
