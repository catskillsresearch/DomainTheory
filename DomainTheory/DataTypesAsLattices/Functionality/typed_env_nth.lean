/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.envR_app


namespace DomainTheory.DataTypesAsLattices

































theorem typed_env_nth {t : Pomega} (ht : typed t envR) (n : ℕ) :
    typed (funOf t (ofNat n)) lambR := by
  have ht' : t = graph (fun m => funOf lambR (funOf t m)) := by
    simpa [typed, envR_app] using ht
  have : funOf t (ofNat n) = funOf lambR (funOf t (ofNat n)) := by
    nth_rw 1 [ht']
    exact beta (theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous t)) (ofNat n)
  exact this

end DomainTheory.DataTypesAsLattices
