/-ai
Four natural numbers n₀, n₁, n₂, and m are packed by nesting the pairing function as pair(n₀, pair(n₁, pair(n₂, m))).
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

def pack4 (n0 n1 n2 m : ℕ) : ℕ :=
  Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m))

end DomainTheory.DataTypesAsLattices
