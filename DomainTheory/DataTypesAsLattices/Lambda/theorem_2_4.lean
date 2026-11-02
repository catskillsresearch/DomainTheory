module

public import DomainTheory.DataTypesAsLattices.Lambda.erase

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_2_4

theorem complete (t : Term) (ρ : ℕ → Pomega) :
    interp t ρ = ofComb (erase t) ρ :=
  (erase.correct t ρ).symm

theorem closed (t : Term) :
    IsCombinatory (interp t (fun _ => botElem)) := by
  rw [theorem_2_4.complete]
  refine ofComb.combinatory _ _ fun _ => ?_
  have hbot : funOf predC zeroC = botElem := by
    rw [predC.app]; exact eq_2_6
  exact hbot ▸ IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end theorem_2_4

theorem theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩

end DomainTheory.DataTypesAsLattices
