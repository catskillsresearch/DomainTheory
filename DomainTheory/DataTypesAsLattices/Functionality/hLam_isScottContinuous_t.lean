/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion_isScottContinuous_t


namespace DomainTheory.DataTypesAsLattices















































theorem hLam_isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun t =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))
    (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun t x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        theorem_1_3
          (f := funOf (funOf H (funOf (expPayload e) (ofNat 1))))
          (g := fun t => updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))
          (funOf_isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
          (updateEnvUnion_isScottContinuous_t x
            (funOf (expPayload e) (ofNat 0)))))

end DomainTheory.DataTypesAsLattices
