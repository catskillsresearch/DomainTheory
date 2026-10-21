/-ai
Applying the bar step of B to u yields the graph of the bar step body at B and u.

This is beta reduction. Continuity of the outer graph in its first argument holds because, for each second argument, the bar step body is Scott continuous in u.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody_isScottContinuous_u

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barStep_app (B u : Pomega) :
    funOf (barStep B) u = graph (fun x => barStepBody B u x) :=
  beta (graph_const_isScottContinuous (fun u x => barStepBody B u x)
    (fun x => barStepBody_isScottContinuous_u B x)) u

end DomainTheory.DataTypesAsLattices
