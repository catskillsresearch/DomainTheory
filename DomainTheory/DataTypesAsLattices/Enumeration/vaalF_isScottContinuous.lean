/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


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
