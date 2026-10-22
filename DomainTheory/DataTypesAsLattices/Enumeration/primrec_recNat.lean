module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem primrec_recNat (v : ℕ → ℕ) (hv : Primrec v) :
    Primrec (recNat v) := by
  unfold recNat
  exact primrec_applyNat.comp hv (primrec_num.comp hv)

end DomainTheory.DataTypesAsLattices
