
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
