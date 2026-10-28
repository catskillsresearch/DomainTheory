module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.unionCode
public import DomainTheory.DataTypesAsLattices.Enumeration.fin
public import DomainTheory.DataTypesAsLattices.Enumeration.condCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

noncomputable def myhillCase2Code (j n m : ℕ) : ℕ :=
  applyNat (applyNat unionCode (fin j))
    (applyNat (applyNat (applyNat condCode n) n) m)

end DomainTheory.DataTypesAsLattices
