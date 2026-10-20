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
import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono_incl
import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono_incl_apply


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

















































section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]



omit [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y] in
/-- **Scott 1972, Lemma 3.9 (inclusion at infimum level).** Used in the inverse-limit
argument (Theorem 4.4). -/
theorem lemma_3_9_incl_inf {e : X → Y} (P : IsContinuousLatticeProjection D D')
    {f : X → D} {g : X → D'} (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    P.incl (scottSubspaceExtendInf e f U) ≤ scottSubspaceExtendInf e g U :=
  le_trans (scottSubspaceExtendInf_mono_incl_apply (e := e) (f := f) U P)
    (scottSubspaceExtendInf_mono_incl (e := e) (f := f) (g := g) P hfg U)

end SubspaceExtension
end DomainTheory.ContinuousLattice
