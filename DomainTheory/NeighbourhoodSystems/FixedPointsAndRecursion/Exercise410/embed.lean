/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `𝒟`-element obtained from a `Dₐ`-filter by upward closure in `𝒟`. -/
def embed (a : V.Element) (g : (relSystem a).Element) : V.Element where
  mem X := V.mem X ∧ ∃ W, a.mem W ∧ g.mem W ∧ W ⊆ X
  sub := fun h => h.1
  master_mem := ⟨V.master_mem, V.master, a.master_mem, g.master_mem, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hVX, Wx, haWx, hgWx, hWxX⟩ ⟨hVY, Wy, haWy, hgWy, hWyY⟩
    have haWxy : a.mem (Wx ∩ Wy) := a.inter_mem haWx haWy
    have hgWxy : g.mem (Wx ∩ Wy) := g.inter_mem hgWx hgWy
    have hsub : Wx ∩ Wy ⊆ X ∩ Y := Set.inter_subset_inter hWxX hWyY
    refine ⟨V.inter_mem hVX hVY (a.sub haWxy) hsub, Wx ∩ Wy, haWxy, hgWxy, hsub⟩
  up_mem := by
    rintro X Y ⟨hVX, W, haW, hgW, hWX⟩ hVY hXY
    exact ⟨hVY, W, haW, hgW, subset_trans hWX hXY⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
