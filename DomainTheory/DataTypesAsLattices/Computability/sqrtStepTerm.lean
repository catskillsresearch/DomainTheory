module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sqrtStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond
      (.app (.app (.var 3)
        (.app (.app (.var 4) (.succ (.var 2))) (.succ (.var 2))))
        (.var 0))
      (.var 2)
      (.succ (.var 2)))))

end DomainTheory.DataTypesAsLattices
