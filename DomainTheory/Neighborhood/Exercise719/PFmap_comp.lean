/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise719.Basic
import DomainTheory.Neighborhood.Exercise719.comp_witness


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}




/-- **Exercise 7.19 — `ℙ` preserves composition.** `ℙ(g ∘ f) = ℙg ∘ ℙf`. The forward direction
constructs the intermediate `ℙE`-neighbourhood from `comp_witness`; the backward direction merely
threads the existential witnesses. -/
theorem PFmap_comp (g : ApproximableMap W U) (f : ApproximableMap V W) :
    PFmap (g.comp f) = (PFmap g).comp (PFmap f) := by
  apply ApproximableMap.ext
  intro A C
  simp only [PFmap_rel, comp_rel]
  constructor
  · rintro ⟨hA, hC, hbody⟩
    obtain ⟨L, hL, rfl⟩ := hA
    have hpre : ∀ X ∈ L, ∃ Z, Z ∈ C ∧ ∃ Y, f.rel X Y ∧ g.rel Y Z := by
      intro X hX
      obtain ⟨Z, hZC, Y, hfXY, hgYZ⟩ :=
        hbody X ((V.mem_PDunion).mpr ⟨X, hX, hL X hX, subset_rfl⟩)
      exact ⟨Z, hZC, Y, hfXY, hgYZ⟩
    obtain ⟨M, hMmem, hfL, hgM⟩ := comp_witness f g C L hL hpre
    refine ⟨⋃ Y ∈ M, W.upSet Y,
      ⟨⟨L, hL, rfl⟩, ⟨M, hMmem, rfl⟩, ?_⟩, ⟨M, hMmem, rfl⟩, hC, ?_⟩
    · intro X hX
      obtain ⟨X', hX', hXmem, hXsub⟩ := (V.mem_PDunion).mp hX
      obtain ⟨Y, hYM, hrel⟩ := hfL X' hX'
      exact ⟨Y, (W.mem_PDunion).mpr ⟨Y, hYM, hMmem Y hYM, subset_rfl⟩,
        f.mono hrel hXsub subset_rfl hXmem (hMmem Y hYM)⟩
    · intro Y hY
      obtain ⟨Y', hY', hYmem, hYsub⟩ := (W.mem_PDunion).mp hY
      obtain ⟨Z, hZC, hrel⟩ := hgM Y' hY'
      exact ⟨Z, hZC, g.mono hrel hYsub subset_rfl hYmem (g.rel_cod hrel)⟩
  · rintro ⟨B, ⟨hA, hB, hfAB⟩, _, hC, hgBC⟩
    refine ⟨hA, hC, ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hfXY⟩ := hfAB X hX
    obtain ⟨Z, hZC, hgYZ⟩ := hgBC Y hYB
    exact ⟨Z, hZC, Y, hfXY, hgYZ⟩

end DomainTheory.Neighborhood
