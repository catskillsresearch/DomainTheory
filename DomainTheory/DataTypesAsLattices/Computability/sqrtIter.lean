/-ai
The function sqrtIter n is the bounded iteration used to compute the integer square root of n. It sends 0 to 0, and from the value a at k it sends k + 1 to a + 1 when (a + 1) · (a + 1) is at most n and to a otherwise.
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

/-- The bounded iteration used to compute `Nat.sqrt n`. -/
def sqrtIter (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      let a := sqrtIter n k
      if (a + 1) * (a + 1) ≤ n then a + 1 else a

end DomainTheory.DataTypesAsLattices
