module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def Realizes2 (u : Pomega) (p : ℕ → ℕ → ℕ) : Prop :=
  ∀ n m, funOf (funOf u (ofNat n)) (ofNat m) = ofNat (p n m)

end DomainTheory.DataTypesAsLattices
