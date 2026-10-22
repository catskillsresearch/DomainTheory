/-ai
The bar step of an element B is the graph of the map sending u to the graph of the bar step body at B, u, and a variable element.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

def barStep (B : Pomega) : Pomega :=
  graph (fun u => graph (fun x => barStepBody B u x))

end DomainTheory.DataTypesAsLattices
