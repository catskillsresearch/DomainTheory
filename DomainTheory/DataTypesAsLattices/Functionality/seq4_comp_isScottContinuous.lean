/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_comp_isScottContinuous
    {f g h i : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun u => seq4 (f u) (g u) (h u) (i u)) :=
  graph_const_isScottContinuous
    (fun u z =>
      condSet z (f u)
        (condSet (predSet z) (g u)
          (condSet (predSet (predSet z)) (h u)
            (condSet (predSet (predSet (predSet z))) (i u) botElem))))
    (fun z =>
      continuous_nary
        (fun y t => condSet_isScottContinuous_left y t)
        (fun x t => condSet_isScottContinuous_mid x t)
        (fun x y => condSet_isScottContinuous_right x y)
        (const_isScottContinuous z) hf
        (continuous_nary
          (fun y t => condSet_isScottContinuous_left y t)
          (fun x t => condSet_isScottContinuous_mid x t)
          (fun x y => condSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet z)) hg
          (continuous_nary
            (fun y t => condSet_isScottContinuous_left y t)
            (fun x t => condSet_isScottContinuous_mid x t)
            (fun x y => condSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet z))) hh
            (continuous_nary
              (fun y t => condSet_isScottContinuous_left y t)
              (fun x t => condSet_isScottContinuous_mid x t)
              (fun x y => condSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet (predSet (predSet z))))
              hi (const_isScottContinuous botElem)))))

end DomainTheory.DataTypesAsLattices
