/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app2
import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_isGraph
import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app_isGraph
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_sigma_index
import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_app
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_finite


namespace DomainTheory.DataTypesAsLattices






























theorem theorem_7_4_unique (z : Pomega)
    (hη : ∀ f, funOf z f = funOf z (graph (fun y => funOf f y)))
    (hz : ∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) :
    ∃ n, z = Zcomb n := by
  obtain ⟨n, hn⟩ := theorem_7_4_sigma_index z hη hz
  refine ⟨n, ?_⟩
  have hfinite (p : ℕ) :
      funOf z (e p) = funOf (Zcomb n) (e p) := by
    let gp := graph (fun y => funOf (e p) y)
    have hgpGraph : gp = graph (fun y => funOf gp y) := by
      apply graph_ext
      intro y
      exact (normalized_finite_app p y).symm
    have hgpMem : (arrowE emptyE emptyE).mem gp :=
      ⟨hgpGraph, hgpGraph, fun _ _ h => False.elim h⟩
    have hzgpGraph : funOf z gp = graph (fun y => funOf (funOf z gp) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgpMem).1
    have hzFiniteGraph :
        funOf z (e p) = graph (fun y => funOf (funOf z (e p)) y) := by
      rw [hη (e p)]
      exact hzgpGraph
    apply graph_funOf_ext hzFiniteGraph (Zcomb_app_isGraph n (e p))
    intro x
    have hright :
        IsScottContinuous (fun y => Z n (e p) y) :=
      Z_isScottContinuous_right n (e p)
    have hleft :
        IsScottContinuous (fun y => funOf (funOf z (e p)) y) :=
      funOf_isScottContinuous (funOf z (e p))
    have heq := congrFun
      (isScottContinuous_determined hleft hright
        (fun q => theorem_7_4_finite z hη hz hn p q)) x
    simpa [Zcomb_app2] using heq
  have hall (f : Pomega) : funOf z f = funOf (Zcomb n) f := by
    let gf := graph (fun y => funOf f y)
    have hgfGraph : gf = graph (fun y => funOf gf y) := by
      apply graph_ext
      intro y
      exact (beta (funOf_isScottContinuous f) y).symm
    have hgfMem : (arrowE emptyE emptyE).mem gf :=
      ⟨hgfGraph, hgfGraph, fun _ _ h => False.elim h⟩
    have hzgfGraph : funOf z gf = graph (fun y => funOf (funOf z gf) y) :=
      ((theorem_7_1 (arrowE emptyE emptyE) (arrowE emptyE emptyE)).2.1
        (hz emptyE) hgfMem).1
    have hzfGraph :
        funOf z f = graph (fun y => funOf (funOf z f) y) := by
      rw [hη f]
      exact hzgfGraph
    apply graph_funOf_ext hzfGraph (Zcomb_app_isGraph n f)
    intro x
    have hleft :
        IsScottContinuous (fun g => funOf (funOf z g) x) :=
      theorem_1_3 (f := fun u => funOf u x) (g := funOf z)
        (funOf_isScottContinuous_left x)
        (funOf_isScottContinuous z)
    have hright : IsScottContinuous (fun g => Z n g x) :=
      Z_isScottContinuous_left n x
    have heq := congrFun
      (isScottContinuous_determined hleft hright (fun p => by
        have := congrArg (fun w => funOf w x) (hfinite p)
        simpa [Zcomb_app2] using this)) f
    simpa [Zcomb_app2] using heq
  exact graph_funOf_ext (hz emptyE).1 (Zcomb_isGraph n) hall

end DomainTheory.DataTypesAsLattices
