/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
import DomainTheory.ContinuousLattice.FunctionSpaces.corollary_3_4_preservesDirectedSup


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

























/-- **Scott 1972, Corollary 3.4.** The evaluation map `eval : [D → D'] × D → D'`, `(f, x) ↦ f x`,
is (jointly) Scott-continuous. Via Theorem 3.3(b) and Proposition 2.9(b) the Scott topology of the
product lattice is the product of the pointwise topology on `[D → D']` and the Scott topology on
`D`, so this is exactly joint continuity for Scott's product topology. -/
theorem corollary_3_4_jointly_continuous :
    @Continuous (ScottMap D D' × D) D' scottTopologicalSpace scottTopologicalSpace
      (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) :=
  continuous_of_preservesDirectedSup corollary_3_4_preservesDirectedSup

end DomainTheory.ContinuousLattice
