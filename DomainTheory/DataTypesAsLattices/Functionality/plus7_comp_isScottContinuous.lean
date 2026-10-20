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
































theorem plus7_comp_isScottContinuous
    {f0 f1 f2 f3 f4 f5 f6 : Pomega → Pomega}
    (h0 : IsScottContinuous f0) (h1 : IsScottContinuous f1)
    (h2 : IsScottContinuous f2) (h3 : IsScottContinuous f3)
    (h4 : IsScottContinuous f4) (h5 : IsScottContinuous f5)
    (h6 : IsScottContinuous f6) :
    IsScottContinuous (fun z =>
      plus7 (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z)) :=
  graph_const_isScottContinuous
    (fun z u => plus7Body (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z) u)
    (fun u => by
      have htag (i : ℕ) {f : Pomega → Pomega} (hf : IsScottContinuous f) :
          IsScottContinuous (fun z =>
            tagInj i (funOf (f z) (funOf u (ofNat 1)))) :=
        theorem_1_3 (f := tagInj i)
          (g := fun z => funOf (f z) (funOf u (ofNat 1)))
          (tagInj_isScottContinuous i)
          (theorem_1_3 (f := fun w => funOf w (funOf u (ofNat 1))) (g := f)
            (funOf_isScottContinuous_left (funOf u (ofNat 1))) hf)
      exact continuous_nary
        (fun y t => dcondSet_isScottContinuous_left y t)
        (fun x t => dcondSet_isScottContinuous_mid x t)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (const_isScottContinuous (funOf u (ofNat 0))) (htag 0 h0)
        (continuous_nary
          (fun y t => dcondSet_isScottContinuous_left y t)
          (fun x t => dcondSet_isScottContinuous_mid x t)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet (funOf u (ofNat 0)))) (htag 1 h1)
          (continuous_nary
            (fun y t => dcondSet_isScottContinuous_left y t)
            (fun x t => dcondSet_isScottContinuous_mid x t)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet (funOf u (ofNat 0)))))
            (htag 2 h2)
            (continuous_nary
              (fun y t => dcondSet_isScottContinuous_left y t)
              (fun x t => dcondSet_isScottContinuous_mid x t)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[3] (funOf u (ofNat 0))))
              (htag 3 h3)
              (continuous_nary
                (fun y t => dcondSet_isScottContinuous_left y t)
                (fun x t => dcondSet_isScottContinuous_mid x t)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[4] (funOf u (ofNat 0))))
                (htag 4 h4)
                (continuous_nary
                  (fun y t => dcondSet_isScottContinuous_left y t)
                  (fun x t => dcondSet_isScottContinuous_mid x t)
                  (fun x y => dcondSet_isScottContinuous_right x y)
                  (const_isScottContinuous (predSet^[5] (funOf u (ofNat 0))))
                  (htag 5 h5)
                  (continuous_nary
                    (fun y t => dcondSet_isScottContinuous_left y t)
                    (fun x t => dcondSet_isScottContinuous_mid x t)
                    (fun x y => dcondSet_isScottContinuous_right x y)
                    (const_isScottContinuous (predSet^[6] (funOf u (ofNat 0))))
                    (htag 6 h6) (const_isScottContinuous topElem))))))))

end DomainTheory.DataTypesAsLattices
