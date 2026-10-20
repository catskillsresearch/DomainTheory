module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- A combinator realizes a number-theoretic function on numerals. -/
def Realizes (u : Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n, funOf u (ofNat n) = ofNat (p n)

end DomainTheory.DataTypesAsLattices
