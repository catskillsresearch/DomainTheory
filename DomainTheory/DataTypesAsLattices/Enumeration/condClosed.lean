/-ai
The closed conditional term abstracts variables 4, 5, and 6, and forms the conditional of variable 6 with branches variable 4 and variable 5.
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

def condClosed : Term :=
  .lam 4 (.lam 5 (.lam 6 (.cond (.var 6) (.var 4) (.var 5))))

end DomainTheory.DataTypesAsLattices
