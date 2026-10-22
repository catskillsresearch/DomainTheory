/-ai
If an element x of Pω is recursively enumerable, then so is its successor, the set of numbers of the form n + 1 for n in x.

Equality with zero is a computable predicate, and so is its negation. Conjoined with membership of the predecessor in x, the predicate is recursively enumerable. A number that is nonzero and whose predecessor lies in x is the successor of that predecessor. Conversely, a successor witness is nonzero, and on a successor the predecessor is the witness itself.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
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
