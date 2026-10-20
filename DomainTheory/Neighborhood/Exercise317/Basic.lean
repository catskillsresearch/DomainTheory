/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.17 (Scott 1981, PRG-19, §3) — `B` is a retract of `T^∞`

Using the binary system `B` (Example 1.B) and the three-element truth system `T` (Example 1.2),
Scott asks for a **one-one** approximable map `f : B → T^∞` and a map `g : T^∞ → B` with

`g ∘ f = I_B`  and  `f ∘ g ⊑ I_{T^∞}`,

i.e. `B` is a *retract* of `T^∞` (`f` a section, `g` a retraction). He then asks whether `B ≅ T^∞`
and `B ≅ T × B` (the point of the exercise being that retract ≠ isomorphism here).

**The encoding.** A binary string `σ = b₀b₁…b_{k-1}` (a neighbourhood `σΣ*` of `B`) is sent to the
`T^∞`-neighbourhood `encSet σ` that pins copy `i` to the truth value `bitNbhd bᵢ` (`{0}` for `false`,
`{1}` for `true`) for `i < k`, and leaves copies `i ≥ k` free (`Δ_T`). Concretely `encSet σ` is the
*pointwise* set `{(i, t) ∣ ∀ b, σ[i]? = some b → t ∈ bitNbhd b}`.

* `f` relates `σΣ*` to every `T^∞`-neighbourhood weaker than `encSet σ`;
* `g` relates a `T^∞`-neighbourhood `W` to `τΣ*` exactly when `W ⊆ encSet τ`, i.e. `W` already pins
  the first `|τ|` copies to `τ` (decoding the longest gap-free prefix).

`g ∘ f = I_B` (`gf_eq_id`) — decoding recovers the prefix, the key being
`prefix_of_encSet_subset` (`encSet σ ⊆ encSet τ ⟹ τ ⪯ σ`), which uses that `T`-neighbourhoods are
non-empty. `f ∘ g ⊑ I_{T^∞}` (`fg_le_id`) holds because re-encoding a decoded element can only lose
the post-gap information. Hence `f` is one-one (`f_injective`).
-/

namespace DomainTheory.Neighborhood.Exercise317

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap

/-- The truth domain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem
/-- Tokens of `T`: `{0, 1}`. -/
abbrev Token := Example12.Token

/-- The `T`-neighbourhood selected by a bit: `false ↦ {0}`, `true ↦ {1}`. -/
def bitNbhd : Bool → Set Token
  | false => Example12.zero
  | true => Example12.one

theorem bitNbhd_mem (b : Bool) : T.mem (bitNbhd b) := by
  cases b
  · exact Example12.mem_zero
  · exact Example12.mem_one

/-- `T`-neighbourhoods are non-empty (`∅ ∉ T`). -/
theorem T_nbhd_nonempty {F : Set Token} (hF : T.mem F) : F.Nonempty := by
  rcases (Example12.mem_iff F).mp hF with rfl | rfl | rfl
  · exact ⟨0, by simp [Example12.master]⟩
  · exact ⟨0, by simp [Example12.zero]⟩
  · exact ⟨1, by simp [Example12.one]⟩

/-! ### The encoding set `encSet σ`. -/

/-- `encSet σ ⊆ ℕ × {0,1}`: pin copy `i` to `bitNbhd σ[i]` for `i < |σ|`, free otherwise. -/
def encSet (σ : Str) : Set (ℕ × Token) := {p | ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b}

@[simp] theorem mem_encSet {σ : Str} {p : ℕ × Token} :
    p ∈ encSet σ ↔ ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b := Iff.rfl

theorem fiber_encSet_some {σ : Str} {i : ℕ} {b : Bool} (h : σ[i]? = some b) :
    fiber (encSet σ) i = bitNbhd b := by
  ext t
  simp only [mem_fiber, mem_encSet]
  constructor
  · intro hh; exact hh b h
  · intro ht b' hb'; rw [h] at hb'; cases hb'; exact ht

theorem fiber_encSet_none {σ : Str} {i : ℕ} (h : σ[i]? = none) :
    fiber (encSet σ) i = Set.univ := by
  ext t
  simp only [mem_fiber, mem_encSet, Set.mem_univ, iff_true]
  intro b hb; rw [h] at hb; exact absurd hb (by simp)

@[simp] theorem encSet_nil : encSet [] = Set.univ := by
  ext p; simp [encSet]

/-- `encSet σ` is a `T^∞`-neighbourhood. -/
theorem encSet_mem (σ : Str) : (iterSys T).mem (encSet σ) := by
  refine ⟨fun i => ?_, σ.length, fun i hi => ?_⟩
  · cases h : σ[i]? with
    | none => rw [fiber_encSet_none h]; exact T.master_mem
    | some b => rw [fiber_encSet_some h]; exact bitNbhd_mem b
  · rw [fiber_encSet_none (List.getElem?_eq_none_iff.mpr hi)]; rfl

/-- A longer prefix encodes to a *smaller* set: `σ ⪯ σ' ⟹ encSet σ' ⊆ encSet σ`. -/
theorem encSet_anti {σ σ' : Str} (h : σ <+: σ') : encSet σ' ⊆ encSet σ := by
  obtain ⟨t, rfl⟩ := h
  rintro ⟨i, x⟩ hp b hb
  have hi : i < σ.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb; exact hlt
  exact hp b (by rw [List.getElem?_append_left hi]; exact hb)

/-! ### Comparability and the prefix recovery lemma. -/

/-- Two prefixes that both bound a common non-empty `T^∞`-neighbourhood agree where both defined. -/
theorem encSet_agree {τ τ' : Str} {W : Set (ℕ × Token)} (hW : (iterSys T).mem W)
    (h : W ⊆ encSet τ) (h' : W ⊆ encSet τ') {i : ℕ} {b b' : Bool}
    (hb : τ[i]? = some b) (hb' : τ'[i]? = some b') : b = b' := by
  obtain ⟨t, ht⟩ := T_nbhd_nonempty (hW.1 i)
  have h1 : t ∈ bitNbhd b := (h ht) b hb
  have h2 : t ∈ bitNbhd b' := (h' ht) b' hb'
  by_contra hne
  cases b <;> cases b' <;> simp_all [bitNbhd, Example12.zero, Example12.one]

theorem comparable_of_agree : ∀ {τ τ' : Str},
    (∀ (i : ℕ) (b b' : Bool), τ[i]? = some b → τ'[i]? = some b' → b = b') → τ <+: τ' ∨ τ' <+: τ
  | [], _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _ => Or.inr (List.nil_prefix)
  | a :: s, a' :: s', hag => by
      have ha : a = a' := hag 0 a a' (by simp) (by simp)
      subst ha
      have hrec : ∀ (i : ℕ) (b b' : Bool), s[i]? = some b → s'[i]? = some b' → b = b' := by
        intro i b b' hb hb'
        exact hag (i + 1) b b' (by simpa using hb) (by simpa using hb')
      rcases comparable_of_agree hrec with h | h
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

/-! ### The section `f : B → T^∞` and retraction `g : T^∞ → B`. -/

/-- **The encoding map `f : B → T^∞`.** Relates the cone `σΣ*` to every `T^∞`-neighbourhood weaker
than `encSet σ`. -/
def f : ApproximableMap B (iterSys T) where
  rel X W := ∃ σ, X = cone σ ∧ (iterSys T).mem W ∧ encSet σ ⊆ W
  rel_dom := fun ⟨σ, hX, _⟩ => hX ▸ memB_cone σ
  rel_cod := fun ⟨_, _, hW, _⟩ => hW
  master_rel := ⟨[], cone_nil.symm, (iterSys T).master_mem, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro X W W' ⟨σ, hX, hWmem, hWsub⟩ ⟨σ', hX', hW'mem, hW'sub⟩
    obtain rfl : σ = σ' := cone_injective (hX.symm.trans hX')
    exact ⟨σ, hX, (iterSys T).inter_mem hWmem hW'mem (encSet_mem σ)
      (Set.subset_inter hWsub hW'sub), Set.subset_inter hWsub hW'sub⟩
  mono := by
    rintro X X' W W' ⟨σ, hX, _, hWsub⟩ hX'X hWW' hX' hW'mem
    obtain ⟨σ', rfl⟩ := hX'
    subst hX
    have hpre : σ <+: σ' := cone_subset_cone.mp hX'X
    exact ⟨σ', rfl, hW'mem, (encSet_anti hpre).trans (hWsub.trans hWW')⟩

/-- **The decoding map `g : T^∞ → B`.** Relates `W` to the cone `τΣ*` exactly when `W ⊆ encSet τ`,
i.e. `W` pins the first `|τ|` copies to `τ`. -/
def g : ApproximableMap (iterSys T) B where
  rel W X := (iterSys T).mem W ∧ ∃ τ, X = cone τ ∧ W ⊆ encSet τ
  rel_dom h := h.1
  rel_cod := fun ⟨_, τ, hX, _⟩ => hX ▸ memB_cone τ
  master_rel := ⟨(iterSys T).master_mem, [], cone_nil.symm, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro W X X' ⟨hW, τ, hX, hWτ⟩ ⟨_, τ', hX', hWτ'⟩
    subst hX; subst hX'
    rcases comparable_of_agree (fun i b b' => encSet_agree hW hWτ hWτ') with hpre | hpre
    · exact ⟨hW, τ', by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr hpre)], hWτ'⟩
    · exact ⟨hW, τ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr hpre)], hWτ⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, τ, hX, hWτ⟩ hW₂W hXX₂ hW₂ hX₂
    obtain ⟨τ₂, rfl⟩ := hX₂
    subst hX
    have hpre : τ₂ <+: τ := cone_subset_cone.mp hXX₂
    exact ⟨hW₂, τ₂, rfl, hW₂W.trans (hWτ.trans (encSet_anti hpre))⟩

/-! ### `g ∘ f = I_B` and `f ∘ g ⊑ I_{T^∞}`. -/
end DomainTheory.Neighborhood.Exercise317
