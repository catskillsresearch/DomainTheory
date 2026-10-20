/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
import DomainTheory.DataTypesAsLattices.Closures.squarePair_mono


namespace DomainTheory.DataTypesAsLattices































theorem Icomb_subset_boxTensor {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxTensor a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : squarePair (squareFst (e n)) (squareSnd (e n)) ⊆
      squarePair (funOf a (squareFst (e n))) (funOf b (squareSnd (e n))) := by
    refine squarePair_mono ?_ ?_
    · have := funOf_monotone_left ha.1 (squareFst (e n))
      rwa [Icomb_app] at this
    · have := funOf_monotone_left hb.1 (squareSnd (e n))
      rwa [Icomb_app] at this
  refine ⟨n, m, rfl, ?_⟩
  exact hsub (by simpa [eq_5_8] using hm)

end DomainTheory.DataTypesAsLattices
