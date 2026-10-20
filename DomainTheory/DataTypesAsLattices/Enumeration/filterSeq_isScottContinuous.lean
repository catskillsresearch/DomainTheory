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



























theorem filterSeq_isScottContinuous :
    IsScottContinuous fun v =>
      graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)) :=
  graph_const_isScottContinuous
    (fun v j => funOf filterRealizer (funOf (funOf pairComb v) j))
    (fun j =>
      theorem_1_3 (f := fun w => funOf filterRealizer w)
        (g := fun v => funOf (funOf pairComb v) j)
        (funOf_isScottContinuous filterRealizer)
        (theorem_1_3 (f := fun w => funOf w j) (g := fun v => funOf pairComb v)
          (funOf_isScottContinuous_left j)
          (funOf_isScottContinuous pairComb)))

end DomainTheory.DataTypesAsLattices
