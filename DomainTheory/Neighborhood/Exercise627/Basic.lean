/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Lemma615

/-!
# Exercise 6.27 (Scott 1981, PRG-19, §6) — which subsystem relations hold

> **EXERCISE 6.27.** Which of the following relationships are true:
> `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)`;  `𝒟 ⊴ 𝒟 × ℰ`;
> `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)`;  `𝒟 ⊴ 𝒟 ⊕ ℰ`;
> `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)`;  `𝒟 ⊴ 𝒟 ⊗ ℰ` ?

Here `⊴` is Scott's *embeds-as-a-subdomain* relation of Lemma 6.15 (`Trianglelefteq`): `D ⊴ E`
means `D ≅ᴰ D'` for some `D' ◁ E`. We use the concrete `{0,1}*` constructions of Exercises 6.19/6.21
(`sumTok`, `prodTok`, `oplusTok`, `otimesTok`) and the function spaces `funSpace` / `strictFun`.

**Answer.** The first five hold for all `𝒟, ℰ`; the last fails in general.

| relation | verdict | name |
| --- | --- | --- |
| `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)` | **true** | `otimes_trianglelefteq_prod` (in fact `otimesTok ◁ prodTok`) |
| `𝒟 ⊴ 𝒟 × ℰ` | **true** | `fst_trianglelefteq_prod` |
| `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)` | **true** | `oplus_trianglelefteq_sum` (in fact `oplusTok ◁ sumTok`) |
| `𝒟 ⊴ 𝒟 ⊕ ℰ` | **true** | `inl_trianglelefteq_oplus` |
| `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` | **true** | `strictFun_trianglelefteq_funSpace` |
| `𝒟 ⊴ 𝒟 ⊗ ℰ` | **false in general** | `not_trianglelefteq_otimes_unit` |

The smash product collapses the bottom: pairing anything with `⊥_ℰ` is `⊥`. So `𝒟` embeds in
`𝒟 ⊗ ℰ` only when `ℰ` contributes a (finite) non-bottom point; for the trivial `ℰ = 𝟙` we have
`𝒟 ⊗ 𝟙 ≅ 𝟙`, refuting the universal claim.

All parts are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`) except `(4)`
(`inl_trianglelefteq_oplus`), whose `oplus_mem_leftN` decides the genuinely-undecidable test
`X = Δ₀` over an arbitrary system and so depends on `Classical.choice`.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## (1) `(𝒟 ⊗ ℰ) ◁ (𝒟 × ℰ)` — the smash is literally a subsystem of the product

The smash `otimesTok` has the *same* master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ = prodTokNbhd Δ₀ Δ₁` and its proper
neighbourhoods `prodTokNbhd X Y` (with `X ≠ Δ₀`, `Y ≠ Δ₁`) are a sub-family of the product's
neighbourhoods. The consistency clause is inherited because intersections stay off the boundary. -/

/-! ## (2) `𝒟 ⊴ 𝒟 × ℰ` — first-factor projection pair

`𝒟` is not literally a subsystem of `𝒟 × ℰ` (the neighbourhoods have a different shape), but it
embeds via the projection pair `i(X) = (X, ⊥)`, `j(W) = fst W`. Concretely we send `X ∈ 𝒟` to the
product neighbourhood `prodTokNbhd X Δ₁` (pair `X` with all of `ℰ`); the embedding/projection are the
two refinement relations against that neighbourhood, exactly as in Proposition 6.12. -/

/-- The injection `i : 𝒟 → 𝒟 × ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟×ℰ ∧ (X,Δ₁) ⊆ W`. -/
def fstInj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap D₀ (prodTok D₀ D₁) where
  rel X W := D₀.mem X ∧ (prodTok D₀ D₁).mem W ∧ prodTokNbhd X D₁.master ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (prodTok D₀ D₁).master_mem, subset_rfl⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (prodTok D₀ D₁).inter_mem hW hW' (prodTok_mem_prodTokNbhd hX D₁.master_mem)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((prodTokNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩).trans hsub).trans hWW'⟩

/-- The projection `j : 𝒟 × ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟×ℰ ∧ X ∈ 𝒟 ∧ W ⊆ (X,Δ₁)`. -/
def fstProj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap (prodTok D₀ D₁) D₀ where
  rel W X := (prodTok D₀ D₁).mem W ∧ D₀.mem X ∧ W ⊆ prodTokNbhd X D₁.master
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prodTok D₀ D₁).master_mem, D₀.master_mem, subset_rfl⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    obtain ⟨A, B, hA, hB, rfl⟩ := hW
    have hAX : A ⊆ X := (prodTokNbhd_subset_iff.mp hsub).1
    have hAX' : A ⊆ X' := (prodTokNbhd_subset_iff.mp hsub').1
    exact ⟨prodTok_mem_prodTokNbhd hA hB, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
      prodTokNbhd_subset_iff.mpr ⟨Set.subset_inter hAX hAX', D₁.sub_master hB⟩⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans (prodTokNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩))⟩

/-! ## (3) `(𝒟 ⊕ ℰ) ◁ (𝒟 + ℰ)` — the coalesced sum is literally a subsystem of the sum

`oplusTok` drops the improper copies `0Δ₀`, `1Δ₁` of `sumTok`; what remains is a sub-family, and
consistency is inherited (cross-tag intersections are empty, hence not `sumTok`-neighbourhoods). -/

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-! ## (4) `𝒟 ⊴ 𝒟 ⊕ ℰ` — left-injection projection pair

Unlike the product, the coalesced sum *identifies* the two bottoms, so the embedding of `𝒟` must
send `⊥_𝒟 = Δ₀` to the shared bottom `sumTokMaster` and a proper `X` to its left copy `0X`. We
package this in `leftN X` (`= 0X` for proper `X`, `= sumTokMaster` for `X = Δ₀`).

Distinguishing the two cases is exactly the test `X = Δ₀`, which is undecidable for an arbitrary
neighbourhood; consequently the single lemma `oplus_mem_leftN` — and only it — uses `Classical.em`.
This is genuinely unavoidable at this level of generality (Scott's tokens are concrete and decidable,
but we work over arbitrary `NeighborhoodSystem`s), so `inl_trianglelefteq_oplus` depends on
`Classical.choice` (called out in the axiom audit). Every other part of Exercise 6.27 is choice-free. -/

/-- The left-copy generator: `0X` for proper `X`, the shared bottom `sumTokMaster` for `X = Δ₀`. The
set-builder `{w ∣ w ∈ sumTokMaster ∧ X = Δ₀}` keeps the *definition* choice-free. -/
def leftN (D₀ D₁ : NeighborhoodSystem Str) (X : Set Str) : Set Str :=
  embBit false X ∪ {w | w ∈ sumTokMaster D₀ D₁ ∧ X = D₀.master}

theorem embF_subset_leftN {X : Set Str} : embBit false X ⊆ leftN D₀ D₁ X :=
  Set.subset_union_left

theorem leftN_master : leftN D₀ D₁ D₀.master = sumTokMaster D₀ D₁ := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨hw, -⟩)
    · exact embF_subset_sumTokMaster D₀.master_mem hw
    · exact hw
  · exact fun w hw => Or.inr ⟨hw, rfl⟩

theorem leftN_proper {X : Set Str} (hne : X ≠ D₀.master) : leftN D₀ D₁ X = embBit false X := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨-, hXm⟩)
    · exact hw
    · exact absurd hXm hne
  · exact embF_subset_leftN

theorem X_eq_master_of_nil_mem_leftN {X : Set Str} (h : ([] : Str) ∈ leftN D₀ D₁ X) :
    X = D₀.master := by
  rcases h with h | ⟨-, h⟩
  · exact absurd h nil_not_mem_embBit
  · exact h

theorem subset_of_embF_subset_leftN {A X : Set Str} (hA : A ⊆ D₀.master)
    (h : embBit false A ⊆ leftN D₀ D₁ X) : A ⊆ X := by
  intro σ hσ
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', hw'X⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; rw [hw'.2]; exact hw'X
  · rw [hXm]; exact hA hσ

theorem X_eq_master_of_embT_subset_leftN {B X : Set Str} (hB : B.Nonempty)
    (h : embBit true B ⊆ leftN D₀ D₁ X) : X = D₀.master := by
  obtain ⟨σ, hσ⟩ := hB
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', -⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; exact absurd hw'.1 (by decide)
  · exact hXm

theorem leftN_subset_iff {X X' : Set Str} (hX : D₀.mem X) (hX' : D₀.mem X') :
    leftN D₀ D₁ X ⊆ leftN D₀ D₁ X' ↔ X ⊆ X' := by
  constructor
  · intro h
    exact subset_of_embF_subset_leftN (D₀.sub_master hX) (embF_subset_leftN.trans h)
  · intro hXX'
    rintro w (⟨w', rfl, hw'⟩ | ⟨hw, hXm⟩)
    · exact embF_subset_leftN ⟨w', rfl, hXX' hw'⟩
    · exact Or.inr ⟨hw, Set.Subset.antisymm (D₀.sub_master hX') (hXm ▸ hXX')⟩

/-- The **only** classical step in Exercise 6.27: `leftN X` is an `𝒟 ⊕ ℰ`-neighbourhood. The proof
splits on the (undecidable for arbitrary `X`) test `X = Δ₀`. -/
theorem oplus_mem_leftN {X : Set Str} (hX : D₀.mem X) :
    (oplusTok D₀ D₁ h₀ h₁).mem (leftN D₀ D₁ X) := by
  by_cases h : X = D₀.master
  · rw [h, leftN_master]; exact (oplusTok D₀ D₁ h₀ h₁).master_mem
  · rw [leftN_proper h]; exact oplusTok_mem_embF hX h

/-- The injection `i : 𝒟 → 𝒟 ⊕ ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟⊕ℰ ∧ leftN X ⊆ W`. -/
def inlInj : ApproximableMap D₀ (oplusTok D₀ D₁ h₀ h₁) where
  rel X W := D₀.mem X ∧ (oplusTok D₀ D₁ h₀ h₁).mem W ∧ leftN D₀ D₁ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (oplusTok D₀ D₁ h₀ h₁).master_mem, leftN_master.le⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (oplusTok D₀ D₁ h₀ h₁).inter_mem hW hW' (oplus_mem_leftN hX)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((leftN_subset_iff hX' hX).mpr hX'X).trans (hsub.trans hWW')⟩

/-- The projection `j : 𝒟 ⊕ ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟⊕ℰ ∧ X ∈ 𝒟 ∧ W ⊆ leftN X`. -/
def inlProj : ApproximableMap (oplusTok D₀ D₁ h₀ h₁) D₀ where
  rel W X := (oplusTok D₀ D₁ h₀ h₁).mem W ∧ D₀.mem X ∧ W ⊆ leftN D₀ D₁ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(oplusTok D₀ D₁ h₀ h₁).master_mem, D₀.master_mem, leftN_master.ge⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    rcases hW with rfl | ⟨A, hA, hAne, rfl⟩ | ⟨B, hB, hBne, rfl⟩
    · have hXm := X_eq_master_of_nil_mem_leftN (hsub nil_mem_sumTokMaster)
      have hX'm := X_eq_master_of_nil_mem_leftN (hsub' nil_mem_sumTokMaster)
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨Or.inl rfl, D₀.master_mem, leftN_master.ge⟩
    · have hAX : A ⊆ X := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub
      have hAX' : A ⊆ X' := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub'
      exact ⟨oplusTok_mem_embF hA hAne, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
        (embBit_subset.mpr (Set.subset_inter hAX hAX')).trans embF_subset_leftN⟩
    · have hXm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub
      have hX'm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub'
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨oplusTok_mem_embT hB hBne, D₀.master_mem, by
        rw [leftN_master]; exact embT_subset_sumTokMaster hB⟩
  mono := by
    rintro W W' X X' ⟨_, hX, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans ((leftN_subset_iff hX hX').mpr hXX'))⟩

theorem inlProj_comp_inlInj :
    (inlProj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlInj = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (leftN_subset_iff hX hZ).mp (hsub.trans hsub')⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨leftN D₀ D₁ X, ⟨hX, oplus_mem_leftN hX, subset_rfl⟩,
      oplus_mem_leftN hX, hZ, (leftN_subset_iff hX hZ).mpr hXZ⟩

theorem inlInj_comp_inlProj_le :
    (inlInj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlProj
      ≤ idMap (oplusTok D₀ D₁ h₀ h₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

/-- **Exercise 6.27 (4).** `𝒟 ⊴ 𝒟 ⊕ ℰ`. (Uses `Classical.choice` via `oplus_mem_leftN`.) -/
theorem inl_trianglelefteq_oplus :
    D₀ ⊴ oplusTok D₀ D₁ h₀ h₁ :=
  trianglelefteq_of_projectionPair inlInj inlProj inlProj_comp_inlInj inlInj_comp_inlProj_le

/-! ## (5) `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` — the strict maps embed in all maps

A strict map *is* an approximable map, so `𝒟 →⊥ ℰ` sits inside `𝒟 → ℰ` by inclusion `i`, with the
*strictification* `j` (force `f(⊥) = ⊥`) as its retraction. `strictify f ⊑ f` always, and on a strict
`f` strictification is the identity; this gives the projection-pair laws `j ∘ i = id`,
`i ∘ j ⊑ id`. We work over **arbitrary** systems `V₀, V₁` (not just `Str`); the construction is
choice-free. We realise `i, j` on principal inputs via `ofMono` of the element-level inclusion /
strictification, then identify their element maps using the representations `funSpaceEquiv`
(`|𝒟→ℰ| ≃ ApproximableMap`) and `strictFunEquiv` (`|𝒟→⊥ℰ| ≃ StrictMap`). -/

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Strictification of a map** (on relations): keep `f` but force the master input to the master
output. The resulting map is strict, lies below `f`, and is the identity on strict maps. -/
def strictifyMap (g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Y := g.rel X Y ∧ (X = V₀.master → Y = V₁.master)
  rel_dom h := g.rel_dom h.1
  rel_cod h := g.rel_cod h.1
  master_rel := ⟨g.master_rel, fun _ => rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hg, hs⟩ ⟨hg', hs'⟩
    exact ⟨g.inter_right hg hg', fun hX => by rw [hs hX, hs' hX, Set.inter_self]⟩
  mono := by
    rintro X X' Y Y' ⟨hg, hs⟩ hX'X hYY' hX' hY'
    refine ⟨g.mono hg hX'X hYY' hX' hY', fun hX'm => ?_⟩
    have hX : V₀.mem X := g.rel_dom hg
    have hXm : X = V₀.master := Set.Subset.antisymm (V₀.sub_master hX) (hX'm ▸ hX'X)
    exact Set.Subset.antisymm (V₁.sub_master hY') ((hs hXm) ▸ hYY')

theorem strictifyMap_isStrict (g : ApproximableMap V₀ V₁) : IsStrict (strictifyMap g) :=
  fun _ h => h.2 rfl

/-- The strictification as an element of the *strict* function space's token type. -/
def strictify (g : ApproximableMap V₀ V₁) : StrictMap V₀ V₁ := ⟨strictifyMap g, strictifyMap_isStrict g⟩

/-- Element-level inclusion `|𝒟 →⊥ ℰ| → |𝒟 → ℰ|`. -/
def incl (φ : (strictFun V₀ V₁).Element) : (funSpace V₀ V₁).Element :=
  toFilter (toStrictMap φ).1

/-- Element-level strictification `|𝒟 → ℰ| → |𝒟 →⊥ ℰ|`. -/
def strct (ψ : (funSpace V₀ V₁).Element) : (strictFun V₀ V₁).Element :=
  toStrictFilter (strictify (toApproxMap ψ))

theorem incl_mono : Monotone (incl (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab M hM
  obtain ⟨hMmem, haM⟩ := hM
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : (toStrictMap a).1 ≤ (toStrictMap b).1 := (strictFunEquiv V₀ V₁).monotone hab
  exact hle p.1 p.2 (haM p hp)

theorem strct_mono : Monotone (strct (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab W hW
  obtain ⟨hWmem, haW⟩ := hW
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : toApproxMap a ≤ toApproxMap b := (funSpaceEquiv V₀ V₁).monotone hab
  exact ⟨hle p.1 p.2 (haW p hp).1, (haW p hp).2⟩

/-- The inclusion `i : 𝒟 →⊥ ℰ ↪ 𝒟 → ℰ`. -/
def inclMap : ApproximableMap (strictFun V₀ V₁) (funSpace V₀ V₁) :=
  ofMono (fun _ hW => incl ((strictFun V₀ V₁).principal hW))
    (fun _ _ hW hW' hW'W => incl_mono (((strictFun V₀ V₁).principal_le_iff hW hW').mpr hW'W))

/-- The strictification retraction `j : 𝒟 → ℰ → 𝒟 →⊥ ℰ`. -/
def strctMap : ApproximableMap (funSpace V₀ V₁) (strictFun V₀ V₁) :=
  ofMono (fun _ hM => strct ((funSpace V₀ V₁).principal hM))
    (fun _ _ hM hM' hM'M => strct_mono (((funSpace V₀ V₁).principal_le_iff hM hM').mpr hM'M))

end Part5

/-! ## (6) `𝒟 ⊴ 𝒟 ⊗ ℰ` is **false** in general

The smash product sends `(x, ⊥)` and `(⊥, y)` to the single bottom, so if `ℰ` contributes no proper
neighbourhood the whole product collapses to its bottom. Concretely, for the one-point unit `ℰ = 𝟙`
the system `𝒟 ⊗ 𝟙` has *only* its master as a neighbourhood, hence a one-point element lattice; a
`𝒟` with two distinct points therefore cannot embed. This refutes the universal claim. -/

/-- A concrete two-point domain over `{0,1}*`: neighbourhoods `Set.univ` (`= ⊥`) and `{[]}`. -/
def twoPt : NeighborhoodSystem Str where
  mem X := X = Set.univ ∨ X = {[]}
  master := Set.univ
  master_nonempty := ⟨[], Set.mem_univ _⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro X (rfl | rfl)
    · exact subset_rfl
    · exact Set.subset_univ _
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [Set.univ_inter]; exact Or.inr rfl
    · rw [Set.inter_univ]; exact Or.inr rfl
    · rw [Set.inter_self]; exact Or.inr rfl

/-- The one-point unit domain `𝟙` over `{0,1}*` (only neighbourhood `{[]}`). -/
def unitPt : NeighborhoodSystem Str := (singletonSys ({[]} : Set Str) ⟨[], rfl⟩).sys
end Exercise627
end DomainTheory.Neighborhood
