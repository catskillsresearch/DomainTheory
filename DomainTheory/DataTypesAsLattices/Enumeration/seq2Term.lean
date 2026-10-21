/-ai
The term-level binary sequence constructor of terms a and b is the abstraction, binding variable 8, of the conditional of that variable between a and the conditional of its predecessor between b and the bottom term.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.enumBottomTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Term-level binary sequence constructor. -/
def seq2Term (a b : Term) : Term :=
  .lam 8 (.cond (.var 8) a
    (.cond (.pred (.var 8)) b enumBottomTerm))

end DomainTheory.DataTypesAsLattices
