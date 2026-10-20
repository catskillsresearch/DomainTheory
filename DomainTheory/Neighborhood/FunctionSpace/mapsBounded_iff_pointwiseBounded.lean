/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic
import DomainTheory.Neighborhood.FunctionSpace.le_iff_toElementMap_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
















































/-- **Theorem 3.13(ii) (Scott 1981, PRG-19).** `F` is bounded in `|𝒟₀ → 𝒟₁|` iff `{f(x) ∣ f ∈ F}` is
bounded in `|𝒟₁|` for each `x ∈ |𝒟₀|`. The forward direction is `le_iff_toElementMap_le` (3.13(i))
applied pointwise; the backward direction builds the bound `sSupMaps F`. -/
theorem mapsBounded_iff_pointwiseBounded {F : Set (ApproximableMap V₀ V₁)} :
    MapsBounded F ↔ PointwiseBounded F := by
  constructor
  · intro ⟨h, hh⟩ x
    refine ⟨h.toElementMap x, fun z hz => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hz
    exact (le_iff_toElementMap_le.mp (hh f hf)) x
  · intro hpb
    refine ⟨sSupMaps F hpb, fun f hf X Y hrel => ?_⟩
    have hX : V₀.mem X := f.rel_dom hrel
    have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
    exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hpb hX) ⟨f, hf, rfl⟩) Y hmem⟩

end DomainTheory.Neighborhood
