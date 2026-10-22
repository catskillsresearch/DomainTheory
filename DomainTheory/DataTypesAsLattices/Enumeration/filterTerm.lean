/-ai
The term filterTerm is λm. pred($ (λj. filterRealizer(pair m j)) ⊤). The bound argument is variable 0, the dollar combinator is variable 5, the bound index is variable 1, the filter realizer is variable 3, the pairing combinator is variable 4, and the top element is variable 7.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

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
