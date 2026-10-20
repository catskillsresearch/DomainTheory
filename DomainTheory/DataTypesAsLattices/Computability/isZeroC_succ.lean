module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4














theorem isZeroC_succ (n : ℕ) : funOf isZeroC (ofNat (n + 1)) = ofNat 0 := by
  simp only [isZeroC]
  rw [condC_beta3]
  exact eq_2_7_succ (ofNat 1) (ofNat 0) n

end DomainTheory.DataTypesAsLattices
