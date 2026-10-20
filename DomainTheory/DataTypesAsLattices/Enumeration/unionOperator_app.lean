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
import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_left_isScottContinuous
import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_right_isScottContinuous


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code












theorem unionOperator_app (x y : Pomega) :
    funOf (funOf (graph (fun x => graph (fun y => x ∪ y))) x) y = x ∪ y := by
  have hx : IsScottContinuous (fun x => graph (fun y => x ∪ y)) :=
    graph_const_isScottContinuous (fun x y => x ∪ y)
      (fun y => enumerationUnion_left_isScottContinuous y)
  have h1 : funOf (graph (fun x => graph (fun y => x ∪ y))) x =
      graph (fun y => x ∪ y) :=
    beta hx x
  rw [h1]
  exact beta (enumerationUnion_right_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
