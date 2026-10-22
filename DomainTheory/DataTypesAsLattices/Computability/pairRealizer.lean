/-ai
The pairing realizer of elements u and v is S applied to S applied to K applied to the pairing combinator and to u, and then to v.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.pairComb

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pairRealizer (u v : Pomega) : Pomega :=
  Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ pairComb) ⬝ u) ⬝ v

end DomainTheory.DataTypesAsLattices
