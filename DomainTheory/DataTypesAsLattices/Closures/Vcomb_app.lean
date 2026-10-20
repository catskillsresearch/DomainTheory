/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Vapply_left_isScottContinuous


namespace DomainTheory.DataTypesAsLattices
































theorem Vcomb_app (a : Pomega) :
    funOf Vcomb a = graph (fun x => Vapply a x) :=
  beta (graph_const_isScottContinuous (fun a x => Vapply a x)
    (fun x => Vapply_left_isScottContinuous x)) a

end DomainTheory.DataTypesAsLattices
