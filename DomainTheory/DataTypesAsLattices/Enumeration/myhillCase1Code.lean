module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.interCode
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillFilterCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

noncomputable def myhillCase1Code (n m : ℕ) : ℕ :=
  applyNat (applyNat interCode n) (myhillFilterCode m)

end DomainTheory.DataTypesAsLattices
