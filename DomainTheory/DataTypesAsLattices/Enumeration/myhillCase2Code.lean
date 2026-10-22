/-ai
Appendix case 2. The code myhillCase2Code j n m applies the union code to the finite code of j and to the conditional code applied to n, then to n, then to m. Its value is the union of the finite set e_j with the conditional of the value of m between the value of n and the value of n.
ai-/
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
