module

public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.erase
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_6
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.predC_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩

theorem theorem_2_4.complete (t : Term) (ρ : ℕ → Pomega) :
    interp t ρ = ofComb (erase t) ρ :=
  (erase.correct t ρ).symm

theorem theorem_2_4.closed (t : Term) :
    IsCombinatory (interp t (fun _ => botElem)) := by
  rw [theorem_2_4.complete]
  refine ofComb.combinatory _ _ fun _ => ?_
  have hbot : funOf predC zeroC = botElem := by
    rw [predC.app]; exact eq_2_6
  exact hbot ▸ IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end DomainTheory.DataTypesAsLattices
