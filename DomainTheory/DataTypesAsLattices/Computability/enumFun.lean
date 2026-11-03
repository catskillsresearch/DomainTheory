module

public import Mathlib.Computability.PartrecCode
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Nat.Partrec Code

def enumFun (c : Code) (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 c t.unpair.1).isSome
    then t.unpair.1 + 1
    else 0

end DomainTheory.DataTypesAsLattices
