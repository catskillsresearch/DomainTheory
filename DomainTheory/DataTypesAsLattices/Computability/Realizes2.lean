/-ai
An element u of Pω realizes a binary number-theoretic function p when, for all natural numbers n and m, applying u first to the numeral of n and then to the numeral of m yields the numeral of p(n, m).
ai-/
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

def Realizes2 (u : Pomega) (p : ℕ → ℕ → ℕ) : Prop :=
  ∀ n m, funOf (funOf u (ofNat n)) (ofNat m) = ofNat (p n m)

end DomainTheory.DataTypesAsLattices
