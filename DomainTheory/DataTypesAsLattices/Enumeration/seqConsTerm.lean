/-ai
The term-level sequence cons of a term a with a term xs is the abstraction, binding variable 7, of the conditional of that variable between a and the application of xs to its predecessor.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Term-level sequence cons constructor. -/
def seqConsTerm (a xs : Term) : Term :=
  .lam 7 (.cond (.var 7) a (.app xs (.pred (.var 7))))

end DomainTheory.DataTypesAsLattices
