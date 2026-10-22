module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_interCode
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillFilterCode

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem valNat_myhillCase1Code (n m : ℕ) :
    valNat (myhillCase1Code n m) =
      valNat n ∩ {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  rw [myhillCase1Code, valNat_apply, valNat_apply, valNat_interCode,
    eq_2_17, valNat_myhillFilterCode]

end DomainTheory.DataTypesAsLattices
