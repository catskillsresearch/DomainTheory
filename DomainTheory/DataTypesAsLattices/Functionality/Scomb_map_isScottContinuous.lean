/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_map_isScottContinuous :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v =>
      graph_const_isScottContinuous
        (fun u x => funOf (funOf u x) (funOf v x))
        (fun x =>
          theorem_1_3
            (f := fun t => funOf t (funOf v x))
            (g := fun u => funOf u x)
            (funOf_isScottContinuous_left (funOf v x))
            (funOf_isScottContinuous_left x)))

end DomainTheory.DataTypesAsLattices
