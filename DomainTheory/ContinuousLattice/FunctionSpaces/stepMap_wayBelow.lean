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
import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_le_of_wayBelow


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']




















/-- **The step function is way below `f`.** If `e' ≪ f e`, then `ē[e, e'] ≪ f` in `[D → D']`,
witnessed by the Scott-open set `{g | e' ≪ g e}` (open because suprema in `[D → D']` are pointwise
and `{· ≪ ·}` is inaccessible by directed suprema). -/
theorem stepMap_wayBelow {e : D} {e' : D'} {f : ScottMap D D'}
    (he' : e' ≪ (f : D → D') e) : stepMap e e' ≪ f := by
  refine ⟨{g : ScottMap D D' | e' ≪ (g : D → D') e}, ⟨?_, ?_⟩, he', ?_⟩
  · intro g g' hgg' hg
    exact hg.trans_le (hgg' e)
  · intro F hFne hFdir hmem
    simp only [Set.mem_ofPred_eq, ScottMap.sSup_apply] at hmem
    have hne : (Set.image (fun g : ScottMap D D' => (g : D → D') e) F).Nonempty := hFne.image _
    have hdir : DirectedOn (· ≤ ·) (Set.image (fun g : ScottMap D D' => (g : D → D') e) F) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
      exact ⟨(c : D → D') e, Set.mem_image_of_mem _ hc, hac e, hbc e⟩
    obtain ⟨_, ⟨g, hgF, rfl⟩, hg⟩ := (wayBelow_sSup_iff hne hdir).1 hmem
    exact ⟨g, hgF, hg⟩
  · intro g hg
    exact Set.mem_Ici.2 (stepMap_le_of_wayBelow hg)

end DomainTheory.ContinuousLattice
