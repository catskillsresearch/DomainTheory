/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.MilnerCorrection
import DomainTheory.ContinuousLattice.ScottMaps
import DomainTheory.ContinuousLattice.Injective
import Mathlib.Order.Preorder.Finite
import DomainTheory.ContinuousLattice.Constructions.Basic
import DomainTheory.ContinuousLattice.Constructions.scottExtend_eq_of_continuous
import DomainTheory.ContinuousLattice.Constructions.scottExtend_continuous


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- **Scott 1972, Proposition 2.11.** Every continuous lattice is an injective space under its
induced (Scott) topology. The witness is `scottExtend`, which extends any continuous `f` along
any embedding `e` (`scottExtend_eq_of_continuous`) and is itself continuous
(`scottExtend_continuous`). -/
theorem proposition_2_11 {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace := by
  let : TopologicalSpace E := scottTopologicalSpace
  intro X Y _ _ e he f
  exact ⟨⟨scottExtend e f, scottExtend_continuous hE e f⟩,
    fun x => scottExtend_eq_of_continuous hE e he f f.continuous x⟩

end DomainTheory.ContinuousLattice
