/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import DomainTheory.ContinuousLattice.FunctionSpaceTower.Basic


namespace DomainTheory.ContinuousLattice

universe u


attribute [instance] CLat.str




















theorem towerProj_succ (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) (n : ℕ) :
    let P := towerProj D₀ j₀ n
    (towerProj D₀ j₀ (n + 1)).incl = conjMap P.incl P.retr ∧
      (towerProj D₀ j₀ (n + 1)).retr = conjMap P.retr P.incl := by
  exact ⟨rfl, rfl⟩

end DomainTheory.ContinuousLattice
