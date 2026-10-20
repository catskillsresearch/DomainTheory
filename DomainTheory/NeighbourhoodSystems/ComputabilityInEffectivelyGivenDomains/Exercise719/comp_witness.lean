/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise719.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}




/-- Choice-free gathering of composition witnesses along the generators of the source: from a list
`L` of `𝒟`-neighbourhoods each admitting a `(g∘f)`-witness into `C`, build a single list `M` of
`ℰ`-neighbourhoods covering every `X ∈ L` from the `f`-side and covered into `C` from the `g`-side.
Proved by list recursion `obtain`-ing the witnesses (no choice in a `Prop` goal). -/
theorem comp_witness (f : ApproximableMap V W) (g : ApproximableMap W U) (C : Set (Set γ)) :
    ∀ (L : List (Set α)), (∀ X ∈ L, V.mem X) →
      (∀ X ∈ L, ∃ Z, Z ∈ C ∧ ∃ Y, f.rel X Y ∧ g.rel Y Z) →
      ∃ M : List (Set β), (∀ Y ∈ M, W.mem Y) ∧
        (∀ X ∈ L, ∃ Y ∈ M, f.rel X Y) ∧ (∀ Y ∈ M, ∃ Z ∈ C, g.rel Y Z) := by
  intro L
  induction L with
  | nil =>
    intro _ _
    refine ⟨[], ?_, ?_, ?_⟩
    · intro Y hY; cases hY
    · intro X hX; cases hX
    · intro Y hY; cases hY
  | cons X L ih =>
    intro hL hpre
    obtain ⟨Zx, hZxC, Yx, hfx, hgx⟩ := hpre X (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨M, hMmem, hfM, hgM⟩ :=
      ih (fun X' hX' => hL X' (List.mem_cons.mpr (Or.inr hX')))
         (fun X' hX' => hpre X' (List.mem_cons.mpr (Or.inr hX')))
    refine ⟨Yx :: M, ?_, ?_, ?_⟩
    · intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY'
      · exact f.rel_cod hfx
      · exact hMmem Y hY'
    · intro X' hX'
      rcases List.mem_cons.mp hX' with rfl | hX''
      · exact ⟨Yx, List.mem_cons.mpr (Or.inl rfl), hfx⟩
      · obtain ⟨Y, hYM, hrel⟩ := hfM X' hX''
        exact ⟨Y, List.mem_cons.mpr (Or.inr hYM), hrel⟩
    · intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY'
      · exact ⟨Zx, hZxC, hgx⟩
      · exact hgM Y hY'

end DomainTheory.Neighborhood
