/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74

@[expose] public section

/-!
# Exercise 7.17 (Scott 1981, PRG-19, §7) — Part 1: all the Example 6.1 combinators for `D^§`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.17.** Complete the proof of 7.7 for showing that `D^§` is effectively given if `D` is.
> Include all the combinators of 6.1. Prove also that if `E` is effectively given and `u : D → E` and
> `v : E × E → E` are computable, then the unique strict mapping `g : D^§ → E`, where
> `g(in x) = u(x)` and `g(pair(y, z)) = v(g(y), g(z))`, is a computable mapping.

(Scott's text prints "6.2"; the construct `D^§` and its combinators are Example **6.1**, and 7.7 is
itself stated "all the combinators of Example 6.1", so we read it as 6.1.)

`Proposition77.dsharp_isEffectivelyGiven` already gives the first clause (`D^§` effectively given), and
`Combinators77.lean` did **a selection** of the combinators (`inSharp = λx. x^§`, and the pair-part
first projection `proj₀`). **This file finishes Part 1** — the *full* set of Example 6.1's algebra
combinators, each as an `ApproximableMap` that is `IsComputableMap` w.r.t. the canonical
presentation(s):

* **`proj1Map`** — the second projection of the pair part, `proj₁ : D^§ → D^§`
  (`proj1_toElementMap_pairSharp : proj₁(⟨x, y⟩^§) = y`); computable via the right-child reindex
  (`proj1_isComputable`). The exact mirror of `Combinators77.proj0Map`.
* **`pairSharpMap`** — Scott's pairing constructor `pair : D^§ × D^§ → D^§` as a joint approximable
  map out of the product `prod (D^§) (D^§)` (`pairSharpMap_toElementMap : pair(x, y) ↦ ⟨x, y⟩^§`,
  i.e. `Example61.pairSharp`); computable because its index relation is exactly
  `V_{2·⟨a,b⟩+2} ⊆ V_k` (`pairSharp_isComputable`), a recursive slice of `D^§`'s inclusion decider.

Together with `inSharpMap`/`proj0Map` this is the complete combinator set of the domain equation
`D^§ ≅ D + (D^§ × D^§)`: the two injections `in`, `pair` and the two pair-part projections.

The **second clause** of 7.17 (the universal strict catamorphism `g : D^§ → E` and its computability)
is a separate, larger development handled subsequently.

As in `Combinators77.lean`, all `ApproximableMap` **data** and the **faithfulness** theorems are
choice-free `⊆ {propext, Quot.sound}`; only the `IsComputableMap` proofs route through `Classical`
(set reasoning over the arbitrary carrier `α`, inherited from `incl_computable`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-! ### `proj₁ : D^§ → D^§` (second projection of the pair part). -/

/-- **The second projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `Q`; everywhere else it returns `⊥ = {Γ}`. The exact mirror of `proj0Map`
with the *second* component: `W proj₁ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ Q ⊆ Z`. -/
def proj1Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hQZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hQZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hQZ⟩⟩
      · have hQQ : Qq = Qq' := (embPair_injective (hWeq.symm.trans hWeq')).2
        have hQsub : Qq ⊆ Z ∩ Z' := Set.subset_inter hQZ (by rw [hQQ]; exact hQZ')
        have hMemQ : MemS D Qq := (memS_embPair_inv hD (hWeq ▸ hW)).2
        exact ⟨hW, memS_inter hD hZ hZ' hMemQ hQsub, Or.inr ⟨Pp, Qq, hWeq, hQsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hQZ⟩
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hZ'mem) hZZ')
    · subst hWeq
      cases hW'mem with
      | gamma =>
        exact absurd (Set.Subset.antisymm (memS_subset_gamma hW) hW'W)
          (embPair_ne_Gamma D hD Pp Qq)
      | @zero X hX =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        rcases hW'W (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
          ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
      | @pair Pp' Qq' hP' hQ' =>
        obtain ⟨-, hQ'Q⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hQZ (hQ'Q hz))⟩

@[simp] theorem proj1Map_rel {W Z : Set (List Bool × α)} :
    (proj1Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z) := Iff.rfl

/-! ### `pair : D^§ × D^§ → D^§` (Example 6.1's pairing constructor `⟨·, ·⟩^§`).

This is a *joint* combinator, so it is an approximable map out of the product `D^§ × D^§`. On the
product neighbourhood `A ∪ B` (over `α ⊕ α`) it returns `1·A ∪ 2·B` (= `embPair A B`); the master
input `Δ ∪ Δ` maps to `Γ` (since `embPair Γ Γ ⊆ Γ`). -/

/-- **Example 6.1's pairing constructor `pair : D^§ × D^§ → D^§`, as a joint approximable map.**
`(A ∪ B) pair W ↔ A, B ∈ 𝒟^§ ∧ W ∈ 𝒟^§ ∧ 1·A ∪ 2·B ⊆ W` (with `A ∪ B = prodNbhd A B`). -/
def pairSharpMap : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) where
  rel V W := (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
    ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod (Dsharp D hD) (Dsharp D hD)).master_mem, MemS.gamma,
    ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl, embPair_subset_Gamma subset_rfl subset_rfl⟩⟩
  inter_right := by
    rintro V W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ ⟨-, hW', A', B', hA', hB', heq, hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hV, memS_inter hD hW hW' (MemS.pair hA hB) (Set.subset_inter hsub hsub'),
      A, B, hA, hB, rfl, Set.subset_inter hsub hsub'⟩
  mono := by
    rintro V V' W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ hV'V hWW' hV'mem hW'mem
    obtain ⟨A', B', hA', hB', rfl⟩ := hV'mem
    obtain ⟨hA'A, hB'B⟩ := prodNbhd_subset_iff.mp hV'V
    exact ⟨prod_mem_prodNbhd hA' hB', hW'mem, A', B', hA', hB', rfl,
      (embPair_subset.mpr ⟨hA'A, hB'B⟩).trans (hsub.trans hWW')⟩

@[simp] theorem pairSharpMap_rel {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    {W : Set (List Bool × α)} :
    (pairSharpMap hD).rel V W ↔
      (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
        ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W := Iff.rfl
end Proposition77
end DomainTheory.NeighbourhoodSystems
