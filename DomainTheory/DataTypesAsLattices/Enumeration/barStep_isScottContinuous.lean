/-ai
The bar step is Scott continuous.

The outer graph is Scott continuous in its parameter because, for each middle argument, the inner graph is Scott continuous in that parameter by Scott continuity of the bar step body in B.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody_isScottContinuous_B

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem barStep_isScottContinuous : IsScottContinuous barStep :=
  graph_const_isScottContinuous
    (fun B u => graph (fun x => barStepBody B u x))
    (fun u => graph_const_isScottContinuous
      (fun B x => barStepBody B u x)
      (fun x => barStepBody_isScottContinuous_B u x))

end DomainTheory.DataTypesAsLattices
