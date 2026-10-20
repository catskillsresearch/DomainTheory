/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices






















theorem eta2_map_isScottContinuous (f : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf (funOf f x) y)) :=
  graph_const_isScottContinuous
    (fun x y => funOf (funOf f x) y)
    (fun y =>
      theorem_1_3
        (f := fun t => funOf t y)
        (g := funOf f)
        (funOf_isScottContinuous_left y)
        (funOf_isScottContinuous f))

end DomainTheory.DataTypesAsLattices
