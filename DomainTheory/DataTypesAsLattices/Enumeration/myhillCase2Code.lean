module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
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

/-- Appendix case 2: `u(m)` with `val(u m) = e_j ∪ (val m ⊃ val n, val n)`. -/
noncomputable def myhillCase2Code (j n m : ℕ) : ℕ :=
  applyNat (applyNat unionCode (fin j))
    (applyNat (applyNat (applyNat condCode n) n) m)

end DomainTheory.DataTypesAsLattices
