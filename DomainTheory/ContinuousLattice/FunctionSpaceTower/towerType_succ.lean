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





/-- `D_{n+1}` is *definitionally* the function space `[Dₙ → Dₙ]`. -/
theorem towerType_succ (D₀ : CLat.{u}) (n : ℕ) :
    towerType D₀ (n + 1) = ScottMap (towerType D₀ n) (towerType D₀ n) := rfl

end DomainTheory.ContinuousLattice
