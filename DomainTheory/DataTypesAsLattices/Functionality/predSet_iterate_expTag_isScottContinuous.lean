/-ai
For each k, the k-fold iterate of the predecessor, applied to the exponential tag, is Scott continuous.

Induct on k. The zero iterate is left continuity of application at the numeral 0. At a successor, Theorem 1.3 composes continuity of the predecessor with the inductive map, and the successor law for iteration rewrites the composite as the successor iterate.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem predSet_iterate_expTag_isScottContinuous (k : ℕ) :
    IsScottContinuous (fun e => predSet^[k] (expTag e)) := by
  induction k with
  | zero => exact funOf_isScottContinuous_left (ofNat 0)
  | succ k ih =>
    have h := theorem_1_3 (f := predSet)
      (g := fun e => predSet^[k] (expTag e))
      predSet_isScottContinuous ih
    convert h using 1
    funext e
    exact Function.iterate_succ_apply' predSet k (expTag e)

end DomainTheory.DataTypesAsLattices
