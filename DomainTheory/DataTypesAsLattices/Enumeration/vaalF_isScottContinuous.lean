/-ai
The functional vaalF is Scott continuous.

The graph of a family is Scott continuous in the functional argument once each body is. For a fixed tree code, Theorem 1.3 combines continuity of the conditional in its positive branch, at the application of the code to zero and the G combinator, with the continuous pairing of application in the function and application in the argument at the two children of the code.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem vaalF_isScottContinuous : IsScottContinuous vaalF :=
  graph_const_isScottContinuous
    (fun v x =>
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))
    (fun x =>
      theorem_1_3
        (condSet_isScottContinuous_right (funOf x (ofNat 0)) Gcomb)
        (continuous_tuple
          (fun y => funOf_isScottContinuous_left y)
          (fun u => funOf_isScottContinuous u)
          (funOf_isScottContinuous_left
            (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf_isScottContinuous_left
            (funOf (funOf x (ofNat 1)) (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
