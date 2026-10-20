/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
import DomainTheory.DataTypesAsLattices.Functionality.tagInj_isScottContinuous


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_map_isScottContinuous (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    IsScottContinuous (plus7Body a0 a1 a2 a3 a4 a5 a6) := by
  have htag (i : ℕ) (a : Pomega) :
      IsScottContinuous (fun u => tagInj i (funOf a (funOf u (ofNat 1)))) :=
    theorem_1_3 (tagInj_isScottContinuous i)
      (theorem_1_3 (funOf_isScottContinuous a)
        (funOf_isScottContinuous_left (ofNat 1)))
  have hz : IsScottContinuous (fun u => funOf u (ofNat 0)) :=
    funOf_isScottContinuous_left (ofNat 0)
  have hpred : ∀ k, IsScottContinuous
      (fun u => predSet^[k] (funOf u (ofNat 0))) := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih =>
      have h := theorem_1_3 (f := predSet)
        (g := fun u => predSet^[k] (funOf u (ofNat 0)))
        predSet_isScottContinuous ih
      convert h using 1
      funext u
      exact Function.iterate_succ_apply' predSet k (funOf u (ofNat 0))
  refine continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    hz (htag 0 a0)
    (continuous_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (hpred 1) (htag 1 a1)
      (continuous_nary
        (fun y z => dcondSet_isScottContinuous_left y z)
        (fun x z => dcondSet_isScottContinuous_mid x z)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (hpred 2) (htag 2 a2)
        (continuous_nary
          (fun y z => dcondSet_isScottContinuous_left y z)
          (fun x z => dcondSet_isScottContinuous_mid x z)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (hpred 3) (htag 3 a3)
          (continuous_nary
            (fun y z => dcondSet_isScottContinuous_left y z)
            (fun x z => dcondSet_isScottContinuous_mid x z)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (hpred 4) (htag 4 a4)
            (continuous_nary
              (fun y z => dcondSet_isScottContinuous_left y z)
              (fun x z => dcondSet_isScottContinuous_mid x z)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (hpred 5) (htag 5 a5)
              (continuous_nary
                (fun y z => dcondSet_isScottContinuous_left y z)
                (fun x z => dcondSet_isScottContinuous_mid x z)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (hpred 6) (htag 6 a6)
                (const_isScottContinuous topElem)))))))

end DomainTheory.DataTypesAsLattices
