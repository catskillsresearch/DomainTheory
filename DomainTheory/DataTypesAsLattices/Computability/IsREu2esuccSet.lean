module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem IsRE.succSet {x : Pomega} (hx : IsRE x) : IsRE (succSet x) := by
  have heq0 : ComputablePred fun k : ℕ => k = 0 :=
    ⟨inferInstance, (Primrec.eq.decide.comp Primrec.id (Primrec.const 0)).to_comp⟩
  have hne : ComputablePred fun k : ℕ => k ≠ 0 := heq0.not
  have hand : REPred fun k : ℕ => k ≠ 0 ∧ k.pred ∈ x :=
    REPred.and hne.to_re (hx.out.comp Primrec.pred.to_comp)
  constructor
  exact _root_.REPred.of_eq hand (fun k =>
    ⟨fun h => ⟨k.pred, h.2, (Nat.succ_pred_eq_of_ne_zero h.1).symm⟩,
     fun h => by
       obtain ⟨n, hn, hk⟩ := h
       cases k with
       | zero => cases hk
       | succ k => exact ⟨Nat.succ_ne_zero k, by cases hk; exact hn⟩⟩)

end DomainTheory.DataTypesAsLattices
