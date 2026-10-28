module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.recNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_num
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_recNat (v : ℕ → ℕ) (hv : Primrec v) :
    Primrec (recNat v) := by
  unfold recNat
  exact primrec_applyNat.comp hv (primrec_num.comp hv)

end DomainTheory.DataTypesAsLattices
