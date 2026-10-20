/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap










































/-- **No point `g ⟨t,_,_⟩` with `t > 0` is compact**, for *any* neighbourhood system `F` and order
isomorphism `g : Set.Icc (0:ℝ) 1 ≃o F.Element`: the directed family `{g ⟨s,_,_⟩ ∣ 0 ≤ s < t}` has
supremum exactly `g ⟨t,_,_⟩` (`isLUB_Ico` transported through `g`), yet `g ⟨t,_,_⟩` sits strictly
above every member. This is Scott's hint made precise: aside from `⊥` (`t = 0`), `Set.Icc (0:ℝ) 1`
has no finite/compact elements. -/
theorem not_isCompactElt_pos {β : Type} {F : NeighborhoodSystem β}
    (g : Set.Icc (0 : ℝ) 1 ≃o F.Element) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htpos : 0 < t) :
    ¬ IsCompactElt (g ⟨t, ht0, ht1⟩) := by
  intro hcompact
  set S : Set (Set.Icc (0 : ℝ) 1) := {x | x.1 ∈ Set.Ico (0 : ℝ) t} with hSdef
  have hmem0 : (⟨0, le_refl 0, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) ∈ S := ⟨le_refl 0, htpos⟩
  have : Nonempty S := ⟨⟨_, hmem0⟩⟩
  set fam : S → F.Element := fun x => g x.1 with hfamdef
  have hdir : ∀ i j : S, ∃ k : S, fam i ≤ fam k ∧ fam j ≤ fam k := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨⟨⟨max x.1 y.1, le_max_of_le_left x.2.1, (max_lt hx.2 hy.2).le.trans ht1⟩,
      ⟨le_max_of_le_left x.2.1, max_lt hx.2 hy.2⟩⟩, ?_, ?_⟩
    · exact g.monotone (le_max_left x.1 y.1)
    · exact g.monotone (le_max_right x.1 y.1)
  have hSisLUB : IsLUB S (⟨t, ht0, ht1⟩ : Set.Icc (0 : ℝ) 1) := by
    constructor
    · rintro x hx
      exact hx.2.le
    · intro ub hub
      exact (isLUB_Ico htpos).2 (fun y hy =>
        hub (show (⟨y, hy.1, hy.2.le.trans ht1⟩ : Set.Icc (0 : ℝ) 1) ∈ S from hy))
  have hgSisLUB : IsLUB (g '' S) (g ⟨t, ht0, ht1⟩) := g.isLUB_image'.mpr hSisLUB
  have hrange : Set.range fam = g '' S := by
    ext z
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hisLUBfam : IsLUB (Set.range fam) (g ⟨t, ht0, ht1⟩) := hrange ▸ hgSisLUB
  have hisLUBiSup : IsLUB (Set.range fam) (iSupDirected fam hdir) :=
    ⟨fun _ ⟨i, hi⟩ => hi ▸ le_iSupDirected fam hdir i,
      fun y hy => iSupDirected_le fam hdir (fun i => hy ⟨i, rfl⟩)⟩
  have heq : iSupDirected fam hdir = g ⟨t, ht0, ht1⟩ := hisLUBiSup.unique hisLUBfam
  obtain ⟨i, hi⟩ := hcompact fam hdir (le_of_eq heq.symm)
  have hle : (⟨t, ht0, ht1⟩ : Set.Icc (0 : ℝ) 1) ≤ i.1 := g.le_iff_le.mp hi
  exact absurd hle (not_le.mpr i.2.2)

end DomainTheory.NeighbourhoodSystems.Exercise811
