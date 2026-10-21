/-ai
Composition in the semigroup FUN sends elements u and v to the graph of the map taking x to the application of u to the application of v to x.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Composition in the semigroup `FUN`. -/
def enumComp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

end DomainTheory.DataTypesAsLattices
