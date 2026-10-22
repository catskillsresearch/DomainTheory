/-ai
An element u of Pω realizes a number-theoretic function p on numerals when, for every natural number n, applying u to the numeral of n yields the numeral of p(n).
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- A combinator realizes a number-theoretic function on numerals. -/
def Realizes (u : Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n, funOf u (ofNat n) = ofNat (p n)

end DomainTheory.DataTypesAsLattices
