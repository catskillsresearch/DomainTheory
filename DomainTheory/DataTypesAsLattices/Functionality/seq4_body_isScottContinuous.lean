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
































theorem seq4_body_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun z =>
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem)))) :=
  continuous_nary
    (fun y t => condSet_isScottContinuous_left y t)
    (fun x t => condSet_isScottContinuous_mid x t)
    (fun x y => condSet_isScottContinuous_right x y)
    id_isScottContinuous (const_isScottContinuous a)
    (continuous_nary
      (fun y t => condSet_isScottContinuous_left y t)
      (fun x t => condSet_isScottContinuous_mid x t)
      (fun x y => condSet_isScottContinuous_right x y)
      predSet_isScottContinuous (const_isScottContinuous b)
      (continuous_nary
        (fun y t => condSet_isScottContinuous_left y t)
        (fun x t => condSet_isScottContinuous_mid x t)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (f := predSet) (g := predSet)
          predSet_isScottContinuous predSet_isScottContinuous)
        (const_isScottContinuous c)
        (continuous_nary
          (fun y t => condSet_isScottContinuous_left y t)
          (fun x t => condSet_isScottContinuous_mid x t)
          (fun x y => condSet_isScottContinuous_right x y)
          (theorem_1_3 (f := predSet)
            (g := fun z => predSet (predSet z))
            predSet_isScottContinuous
            (theorem_1_3 (f := predSet) (g := predSet)
              predSet_isScottContinuous predSet_isScottContinuous))
          (const_isScottContinuous d) (const_isScottContinuous botElem))))

end DomainTheory.DataTypesAsLattices
