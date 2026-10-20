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















































section Proposition310

open Finset

namespace IsContinuousLatticeProjection








/-- **Scott 1972, Proposition 3.10(iii).** Projections preserve the way-below relation. -/
theorem incl_wayBelow (P : IsContinuousLatticeProjection D D') (hD' : IsContinuousLattice D')
    {x y : D} (h : x ≪ y) : @WayBelow D' _ (P.incl x) (P.incl y) := by
  set W : Set D' := { z' | @WayBelow D' _ z' (P.incl y) }
  have hWne : W.Nonempty := ⟨(⊥ : D'), @bot_wayBelow D' _ (P.incl y)⟩
  have hWdir : DirectedOn (· ≤ ·) W := by
    intro p hp q hq
    exact ⟨p ⊔ q, @WayBelow.sup D' _ p q (P.incl y) hp hq, le_sup_left, le_sup_right⟩
  have hy : y = sSup (Set.image (P.retr : D' → D) W) := by
    rw [← P.retr.preservesDirectedSup_coe W hWne hWdir, @IsContinuousLattice.sSup_wayBelow D' _ hD' (P.incl y),
      P.retr_incl y]
  have hImgne : (Set.image (P.retr : D' → D) W).Nonempty := by
    obtain ⟨z', hz'⟩ := hWne
    exact ⟨P.retr z', z', hz', rfl⟩
  have hImgdir : DirectedOn (· ≤ ·) (Set.image (P.retr : D' → D) W) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    refine ⟨P.retr (a ⊔ b), ⟨a ⊔ b, @WayBelow.sup D' _ a b (P.incl y) ha hb, rfl⟩, ?_, ?_⟩
    · exact P.retr.monotone le_sup_left
    · exact P.retr.monotone le_sup_right
  have hx : x ≪ sSup (Set.image (P.retr : D' → D) W) := by rwa [← hy]
  obtain ⟨prz, hprz, hxpr⟩ := (wayBelow_sSup_iff hImgne hImgdir).1 hx
  obtain ⟨z', hz', rfl⟩ := hprz
  exact @WayBelow.le_trans D' _ (P.incl x) z' (P.incl y)
    (le_trans (P.incl.monotone hxpr.le) (P.incl_retr_le z')) hz'

end IsContinuousLatticeProjection
end Proposition310
end DomainTheory.ContinuousLattice
