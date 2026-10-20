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
