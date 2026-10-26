module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `λm. pred($ (λj. filterRealizer(pair m j)) ⊤)`. -/
def filterTerm : Term :=
  .lam 0 (.pred
    (.app (.app (.var 5)
      (.lam 1 (.app (.var 3) (.app (.app (.var 4) (.var 0)) (.var 1)))))
      (.var 7)))

end DomainTheory.DataTypesAsLattices
