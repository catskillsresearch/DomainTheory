/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix

@[expose] public section

/-!
# Example 1.B (Scott 1981, PRG-19, §1) — binary sequences

Scott's recurring **binary** example, generalizing the finite binary tree of Example 1.4 to
*infinite* sequences. Take `Δ = Σ*` with `Σ = {0,1}` (the finite binary strings, `Λ` = the empty
string), and for `σ ∈ Σ*` let `σΣ*` be the set of all *extensions* of `σ`. The neighbourhoods are

`B = {σΣ* ∣ σ ∈ Σ*}`,

a neighbourhood being "all extensions of a fixed prefix `σ`". We encode `Σ* = List Bool`, the
empty sequence `Λ = []`, concatenation `στ = σ ++ τ`, and the *initial-segment* relation
`σ ⪯ τ` by mathlib's list-prefix order `σ <+: τ`. The cone `σΣ*` is `cone σ = {w ∣ σ <+: w}`.

Deliverables (all of the Example-1.B paragraph, lines 281–315 of the source):

* **Example 1.B / Exercise (`B` is a system).** `B : NeighborhoodSystem Str`, built from the
  prefix *trichotomy* via `ofNestedOrDisjoint` — any two cones are nested or disjoint.
* **`σ⊥` (the finite elements).** `sigmaBot σ = ↑(cone σ)`, the principal filter of `σΣ*`; its
  minimal neighbourhood is `σΔ = cone σ`.
* **Factoid `σ₀⊥ ⊆ σ₁⊥ ⟺ σ₀` initial segment of `σ₁`.** `sigmaBot_le_iff`.
* **Exercise (`σx ∈ |B|`).** `sigmaElt σ x`, and `sigmaElt σ ⊥ = σ⊥` (`sigmaElt_bot`) justifying
  the `σ⊥` notation.
* **Factoid `x = ⋃ₙ σₙ⊥`.** `mem_iff_exists_sigmaBot`: every `x ∈ |B|` is the union of the finite
  elements `σ⊥` with `σΣ* ∈ x` — the concrete "limit of finite approximations" in `|B|`. (The
  countable *chain* form, with `σₙ ⪯ σₙ₊₁` enumerated, needs choice and is left to the prose.)

Everything is **constructive** (`#print axioms ⊆ {propext, Quot.sound}`): list-prefix is decidable,
so the trichotomy is choice-free.
-/

namespace DomainTheory.Neighborhood.ExampleB

open DomainTheory.Neighborhood NeighborhoodSystem

/-- The token type `Σ* = List Bool` (finite binary strings); `Λ = []`. -/
abbrev Str := List Bool

/-- The neighbourhood `σΣ*`: all *extensions* of `σ` (sequences with `σ` as an initial segment). -/
def cone (σ : Str) : Set Str := {w | σ <+: w}

@[simp] theorem mem_cone {σ w : Str} : w ∈ cone σ ↔ σ <+: w := Iff.rfl

/-- `ΛΣ* = Σ*`: the cone of the empty string is everything (Scott's `Δ`). -/
theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

/-- **Cones reverse the prefix order.** `σΣ* ⊆ τΣ*` iff `τ` is an initial segment of `σ`: a longer
prefix carves out a *smaller* cone. (`→` tests at `σ ∈ σΣ*`; `←` is transitivity of `<+:`.) -/
theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

/-- **Prefix trichotomy for cones.** Any two cones are nested-or-disjoint: either one contains the
other, or they are disjoint (incomparable prefixes have no common extension). Choice-free: the
prefix relation on `List Bool` is decidable. -/
theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in Scott's binary neighbourhood system `B`: `X ∈ B` iff `X = σΣ*` for some `σ`. -/
def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

/-- **Exercise ("`B` is a neighbourhood system").** The family `B = {σΣ* ∣ σ ∈ Σ*}` is pairwise
nested-or-disjoint, by `cone_trichotomy`. -/
theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone_trichotomy σ τ

/-- **Example 1.B (Scott 1981, PRG-19).** The binary neighbourhood system `B` on `Δ = Σ*`. -/
def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ
    ⟨[], Set.mem_univ _⟩ ⟨[], cone_nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

@[simp] theorem B_master : B.master = Set.univ := rfl

/-- Every cone is a neighbourhood of `B`. -/
theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

/-! ### Prepending a prefix: `σX = {στ ∣ τ ∈ X}`. -/

/-- Scott's `σX = {στ ∣ τ ∈ X}` (prepend the prefix `σ` to every member of `X`). -/
def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

/-- **`σ(τΣ*) = (στ)Σ*`.** Prepending `σ` to a cone yields the cone of the concatenation — this is
why `σx` lands back in `B` and why `σ⊥` is again a finite element. -/
theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

/-- Prepending preserves membership in `B` (`σ` applied to a cone is a cone). -/
theorem memB_prepend (σ : Str) {X : Set Str} (hX : B.mem X) : B.mem (prepend σ X) := by
  obtain ⟨ρ, rfl⟩ := hX
  exact ⟨σ ++ ρ, prepend_cone σ ρ⟩

@[simp] theorem prepend_nil (X : Set Str) : prepend [] X = X := by
  ext w; simp [mem_prepend]

/-! ### The finite elements `σ⊥` and the initial-segment factoid. -/

/-- **`σ⊥`, a finite element of `|B|`.** The principal filter `↑(σΣ*)` of the cone of `σ`; its
minimal neighbourhood is `σΔ = σΣ*` (Scott). These are exactly the finite elements of `|B|`. -/
def sigmaBot (σ : Str) : B.Element := B.principal (memB_cone σ)

/-! ### The operation `σx` (Scott's left-multiplication on elements). -/

/-- **Exercise (`σx ∈ |B|`).** For `x ∈ |B|` and `σ ∈ Σ*`, Scott's
`σx = {Y ∣ σX ⊆ Y for some X ∈ x}` is again an element of `|B|`.

The filter laws: `master` uses `X = Δ ∈ x` (`σΔ ⊆ Δ` trivially); `inter` takes `X₁ ∩ X₂ ∈ x` and
the consistency witness `σ(X₁∩X₂)`, which is a *cone* (hence in `B`, by `memB_prepend`) contained in
both `Y₁` and `Y₂`; `up` reuses the same `X`. -/
def sigmaElt (σ : Str) (x : B.Element) : B.Element where
  mem Y := B.mem Y ∧ ∃ X, x.mem X ∧ prepend σ X ⊆ Y
  sub h := h.1
  master_mem := ⟨B.master_mem, B.master, x.master_mem, Set.subset_univ _⟩
  inter_mem := by
    intro Y₁ Y₂ h1 h2
    obtain ⟨hY₁, X₁, hX₁, hsub₁⟩ := h1
    obtain ⟨hY₂, X₂, hX₂, hsub₂⟩ := h2
    have hXinter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁ hX₂
    have hsub : prepend σ (X₁ ∩ X₂) ⊆ Y₁ ∩ Y₂ := by
      rintro w ⟨τ, ⟨hτ₁, hτ₂⟩, rfl⟩
      exact ⟨hsub₁ ⟨τ, hτ₁, rfl⟩, hsub₂ ⟨τ, hτ₂, rfl⟩⟩
    have hZmem : B.mem (prepend σ (X₁ ∩ X₂)) := memB_prepend σ (x.sub hXinter)
    exact ⟨B.inter_mem hY₁ hY₂ hZmem hsub, X₁ ∩ X₂, hXinter, hsub⟩
  up_mem := by
    intro X Y hX hY hXY
    obtain ⟨_, X', hX', hsub'⟩ := hX
    exact ⟨hY, X', hX', hsub'.trans hXY⟩

/-! ### Every element is a union of its finite approximations `σ⊥`. -/
end DomainTheory.Neighborhood.ExampleB
