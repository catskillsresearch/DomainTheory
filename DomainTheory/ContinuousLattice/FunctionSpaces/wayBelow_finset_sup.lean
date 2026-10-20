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


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']





















/-- A finite sup of elements way below `g` is way below `g`. -/
theorem wayBelow_finset_sup {ι L : Type*} [CompleteLattice L] {s : Finset ι} {f : ι → L} {g : L}
    (h : ∀ i ∈ s, f i ≪ g) : s.sup f ≪ g :=
  Finset.sup_induction (p := fun a => a ≪ g) (bot_wayBelow g) (fun _ ha _ hb => ha.sup hb) h

end DomainTheory.ContinuousLattice
