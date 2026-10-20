/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app_inl
import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app_inr
import DomainTheory.DataTypesAsLattices.Functionality.sumMed_isGraph


namespace DomainTheory.DataTypesAsLattices















theorem sumMed_rel {A B C : RestrictedEquiv} {f g : Pomega}
    (hf : (arrowE A C).mem f) (hg : (arrowE B C).mem g) :
    (arrowE (sumE A B) C).mem (sumMed f g) := by
  refine ⟨sumMed_isGraph f g, sumMed_isGraph f g, ?_⟩
  intro u v huv
  rcases huv with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
  · have hmu : funOf (sumMed f g) u = funOf f (funOf u (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hu).trans
        (sumMed_app_inl f g _)
    have hmv : funOf (sumMed f g) v = funOf f (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inl f g _)
    rw [hmu, hmv]
    exact hf.2.2 (funOf u (ofNat 1)) (funOf v (ofNat 1)) hA
  · have hmu : funOf (sumMed f g) u = funOf g (funOf u (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hu).trans
        (sumMed_app_inr f g _)
    have hmv : funOf (sumMed f g) v = funOf g (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inr f g _)
    rw [hmu, hmv]
    exact hg.2.2 (funOf u (ofNat 1)) (funOf v (ofNat 1)) hB

end DomainTheory.DataTypesAsLattices
