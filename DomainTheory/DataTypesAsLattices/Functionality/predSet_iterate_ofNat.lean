/-ai
For all k and i, the k-fold predecessor of the numeral k + i is the numeral i.

Induct on k. The zero iterate is the identity. At a successor, the successor law for iteration and the successor law for the predecessor reduce the claim to the inductive hypothesis, after the index is rewritten by the arithmetic identity k + 1 + i = k + i + 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem predSet_iterate_ofNat :
    ∀ k i, predSet^[k] (ofNat (k + i)) = ofNat i
  | 0, i => by
    simp [Function.iterate_zero]
  | k + 1, i => by
    rw [Function.iterate_succ_apply]
    have : k + 1 + i = k + i + 1 := by omega
    rw [this, predSet_ofNat_succ]
    exact predSet_iterate_ofNat k i

end DomainTheory.DataTypesAsLattices
