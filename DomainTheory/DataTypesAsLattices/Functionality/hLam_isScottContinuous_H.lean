/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_H


namespace DomainTheory.DataTypesAsLattices














































theorem hLam_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hLam H e t) :=
  theorem_1_3 (funOf_isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun H x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnvUnion t x (funOf (expPayload e) (ofNat 0))))
      (fun _ => hApply_isScottContinuous_H _ _))

end DomainTheory.DataTypesAsLattices
