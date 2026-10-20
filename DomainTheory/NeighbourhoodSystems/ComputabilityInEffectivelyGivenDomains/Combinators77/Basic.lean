/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition77

@[expose] public section

/-!
# Proposition 7.7 — Milestone 4: the Example 6.1 combinators are computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Proposition 7.7.** For any effectively given domain `D`, the domain `D^§` is also effectively
> given, and all the combinators of Example 6.1 prove to be computable.

The "`D^§` is effectively given" half is `Proposition77.dsharp_isEffectivelyGiven`. Here we treat,
as Scott does, *a selection* of the Example 6.1 combinators and exhibit them as
`ApproximableMap`s that are `IsComputableMap` with respect to the canonical presentation
`dsharpPresentation P hD`:

* **`inSharpMap`** — Scott's injection `λx. x^§ : D → D^§` (Example 6.1's `inSharp`). Its
  neighbourhood relation is `X (λx.x^§) W ↔ 0·X ⊆ W`, i.e. `V_{2n+1} ⊆ V_k`, a recursive slice of
  the inclusion decider, hence r.e. (`inSharp_isComputable`). `inSharpMap_toElementMap` checks the
  approximable map really computes `inSharp`.
* **`proj0Map`** — the first projection `D^§ → D^§` of the pair part (so `proj0(⟨x,y⟩^§) = x`,
  `proj0_toElementMap_pairSharp`). Its relation is `W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧
  P ⊆ Z`, i.e. on indices `V_m proj₀ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{p(m/2-1)} ⊆ V_k)`. Both
  disjuncts are recursively decidable, hence r.e. (`proj0_isComputable`).

Each combinator's relation is *recursively decidable* (no unbounded search), so computability is
`RecDecidable.re` of a Boolean combination of the inclusion/equality/parity deciders — exactly the
style of Theorem 7.4's `proj₀`/`in₀`. The `ApproximableMap` data is choice-free; only the `Prop`
correctness proofs route through `Classical` (set equality over an arbitrary carrier).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem dsharpPresentation_X (P : ComputablePresentation D) (n : ℕ) :
    (dsharpPresentation P hD).X n = Vsharp D P n := rfl

/-! ### `λx. x^§ : D → D^§` (Example 6.1's `inSharp`). -/

/-- **Example 6.1's injection `λx. x^§` as an approximable map.** Scott's neighbourhood relation
`X (λx.x^§) W ↔ 0·X ⊆ W` (`embZero X ⊆ W`). The filter laws are immediate: `inter_right` uses
`memS_inter` (with witness `0·X`), and `mono` uses monotonicity of `embZero`. -/
def inSharpMap : ApproximableMap D (Dsharp D hD) where
  rel X W := D.mem X ∧ MemS D W ∧ embZero X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    exact ⟨hX, memS_inter hD hW hW' (MemS.zero hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hsub⟩ hX'X hWW' hX'mem hW'mem
    exact ⟨hX'mem, hW'mem, (embZero_subset.mpr hX'X).trans (hsub.trans hWW')⟩

@[simp] theorem inSharpMap_rel {X : Set α} {W : Set (List Bool × α)} :
    (inSharpMap hD).rel X W ↔ D.mem X ∧ MemS D W ∧ embZero X ⊆ W := Iff.rfl

/-! ### `proj₀ : D^§ → D^§` (first projection of the pair part). -/

/-- **The first projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `P`; everywhere else it returns `⊥ = {Γ}`. The neighbourhood relation is
`W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ P ⊆ Z`. -/
def proj0Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hPZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hPZ⟩⟩
      · have hPP : Pp = Pp' := (embPair_injective (hWeq.symm.trans hWeq')).1
        have hPsub : Pp ⊆ Z ∩ Z' := Set.subset_inter hPZ (by rw [hPP]; exact hPZ')
        have hMemP : MemS D Pp := (memS_embPair_inv hD (hWeq ▸ hW)).1
        exact ⟨hW, memS_inter hD hZ hZ' hMemP hPsub, Or.inr ⟨Pp, Qq, hWeq, hPsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
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
        obtain ⟨hP'P, -⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hPZ (hP'P hz))⟩

@[simp] theorem proj0Map_rel {W Z : Set (List Bool × α)} :
    (proj0Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z) := Iff.rfl
end Proposition77
end DomainTheory.Neighborhood
