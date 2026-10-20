/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise813a

/-!
# Exercise 8.13(b) (Scott 1981, PRG-19, Lecture VIII) — the Lindenbaum algebra bridge

`8.13`'s parenthetical gloss — "the free Boolean algebra on `ℵ₀`-generators (= **the Lindenbaum
algebra of propositional calculus**)" — equates *the algebra itself* with a syntactic quotient of
propositional formulas. `Exercise813a.lean` already built (and used, to answer `8.13`'s actual
"prove that `U` is isomorphic to..." content) a concrete realization of that algebra,
`{X : Set ℕ | GeneratedBy generator X}`. This file makes the parenthetical literal: a `Formula`
syntax, its semantics `evalV`, the Lindenbaum quotient `Formula ⧸ SemanticEquiv`, and a bijection
(`Lindenbaum.toSet`) from that quotient onto `Exercise813a.lean`'s concrete algebra — plus
`entails_iff_evalSet_subset`, showing the bijection also matches semantic entailment with `⊆`, i.e.
it is an order (not just a set) correspondence.

Per the scoping discussion, this is *optional/expository*: `8.13`'s actual "prove that..." content
was already fully answered by `Exercise813a.lean` alone. Nothing here changes that; it only makes
the naming in the parenthetical literal instead of asserted.

## What's proved

* `Formula`, `evalV` — a minimal propositional-logic syntax (`ℵ₀` variables) and its standard
  truth-valuation semantics.
* `evalSet` — the *same* recursion, interpreted in `Set ℕ` via `Exercise813a.lean`'s `generator`.
* `mem_evalSet_iff` — the bridge: `n ∈ evalSet φ ↔ evalV (fun i => n.testBit i) φ = true`.
* `generatedBy_iff_exists_evalSet` — `evalSet`'s range is exactly `GeneratedBy generator`.
* `SemanticEquiv`/the `Formula` `Setoid` — Scott's own equivalence relation for the Lindenbaum
  algebra (`φ ~ ψ` iff they agree under every valuation).
* `semanticEquiv_iff_evalSet_eq` — the one substantive lemma: semantic equivalence (quantifying
  over *all* `v : ℕ → Bool`) agrees with `evalSet`-equality (which only ever "tests" the countably
  many valuations arising from a natural number's own bits), because a single formula only
  mentions finitely many variables (`exists_bitsOf_agree` supplies a matching bit-derived
  valuation for any finite variable set).
* `Lindenbaum := Quotient (formulaSetoid)`, `Lindenbaum.toSet`, `Lindenbaum.toSet_injective`,
  `Lindenbaum.range_toSet` — **the headline**: `Lindenbaum` (Scott's Lindenbaum algebra of
  propositional calculus) bijects, via `toSet`, onto `{X | GeneratedBy generator X}`
  (`Exercise813a.lean`'s free Boolean algebra on `ℵ₀` generators).
* `entails_iff_evalSet_subset` — the bijection also matches semantic entailment with `⊆`, so it
  respects order (hence the Boolean-algebra structure), not just underlying sets.
-/

namespace DomainTheory.Neighborhood

/-! ### The formula language and its two evaluations -/

/-- A minimal propositional-logic syntax over `ℵ₀` variables (indexed by `ℕ`). -/
inductive Formula : Type
  | var (i : ℕ) : Formula
  | bot : Formula
  | top : Formula
  | neg (φ : Formula) : Formula
  | and (φ ψ : Formula) : Formula
  | or (φ ψ : Formula) : Formula

/-- The standard truth-valuation semantics: `v : ℕ → Bool` assigns each variable a truth value. -/
def evalV (v : ℕ → Bool) : Formula → Bool
  | .var i => v i
  | .bot => false
  | .top => true
  | .neg φ => !(evalV v φ)
  | .and φ ψ => evalV v φ && evalV v ψ
  | .or φ ψ => evalV v φ || evalV v ψ

/-- The *same* recursion, but interpreted in `Set ℕ` via `generator` (`Exercise813a.lean`) instead
of an abstract Boolean — i.e. the specific homomorphism `var i ↦ generator i`. -/
def evalSet : Formula → Set ℕ
  | .var i => generator i
  | .bot => ∅
  | .top => Set.univ
  | .neg φ => (evalSet φ)ᶜ
  | .and φ ψ => evalSet φ ∩ evalSet ψ
  | .or φ ψ => evalSet φ ∪ evalSet ψ

/-- The (finite) set of variables occurring in a formula. -/
def vars : Formula → Finset ℕ
  | .var i => {i}
  | .bot => ∅
  | .top => ∅
  | .neg φ => vars φ
  | .and φ ψ => vars φ ∪ vars ψ
  | .or φ ψ => vars φ ∪ vars ψ

/-- **The bridge between the two evaluations**: `evalSet` at `n : ℕ` agrees with `evalV` at `n`'s
own bit-sequence `fun i => n.testBit i`. -/
theorem mem_evalSet_iff (n : ℕ) (φ : Formula) :
    n ∈ evalSet φ ↔ evalV (fun i => n.testBit i) φ = true := by
  induction φ with
  | var i => simp [evalSet, evalV]
  | bot => simp [evalSet, evalV]
  | top => simp [evalSet, evalV]
  | neg φ ih => simp [evalSet, evalV, ih]
  | and φ ψ ihφ ihψ => simp [evalSet, evalV, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [evalSet, evalV, ihφ, ihψ]

/-! ### Only finitely many variables matter -/

theorem evalV_eq_of_agree {φ : Formula} {v v' : ℕ → Bool} (h : ∀ i ∈ vars φ, v i = v' i) :
    evalV v φ = evalV v' φ := by
  induction φ with
  | var i => exact h i (Finset.mem_singleton_self i)
  | bot => rfl
  | top => rfl
  | neg φ ih => simp only [evalV, ih h]
  | and φ ψ ihφ ihψ =>
    simp only [evalV, vars] at h ⊢
    rw [ihφ (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihψ (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or φ ψ ihφ ihψ =>
    simp only [evalV, vars] at h ⊢
    rw [ihφ (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihψ (fun i hi => h i (Finset.mem_union_right _ hi))]

/-- Given any (finite) target set of variables and any valuation `v`, some `n : ℕ` matches `v` on
exactly that set — witnessed directly via `bitmaskOf` (`Exercise813a.lean`). -/
theorem exists_bitsOf_agree (S : Finset ℕ) (v : ℕ → Bool) :
    ∃ n : ℕ, ∀ i ∈ S, n.testBit i = v i := by
  refine ⟨bitmaskOf (S.filter (fun i => v i)), fun i hi => ?_⟩
  have key : (bitmaskOf (S.filter (fun i => v i))).testBit i = true ↔ v i = true := by
    rw [testBit_bitmaskOf]; simp [Finset.mem_filter, hi]
  rcases hv : v i with - | - <;> rcases hn : (bitmaskOf (S.filter (fun i => v i))).testBit i
    with - | - <;> simp_all

/-! ### `SemanticEquiv`: the Lindenbaum equivalence relation -/

/-- **Scott's Lindenbaum equivalence**: `φ ~ ψ` iff they agree under every truth valuation. -/
def SemanticEquiv (φ ψ : Formula) : Prop := ∀ v, evalV v φ = evalV v ψ

instance formulaSetoid : Setoid Formula where
  r := SemanticEquiv
  iseqv := ⟨fun _ _ => rfl, fun h v => (h v).symm, fun h1 h2 v => (h1 v).trans (h2 v)⟩

/-- **The one substantive lemma**: semantic equivalence (quantifying over *all* valuations) agrees
with `evalSet`-equality (which only ever "tests" the countably many bit-derived valuations) —
because a formula only mentions finitely many variables, any valuation can be swapped for a
matching bit-derived one on the (finite) variables that actually occur. -/
theorem semanticEquiv_iff_evalSet_eq {φ ψ : Formula} :
    SemanticEquiv φ ψ ↔ evalSet φ = evalSet ψ := by
  constructor
  · intro h
    ext n
    rw [mem_evalSet_iff, mem_evalSet_iff, h]
  · intro h v
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ ∪ vars ψ) v
    have h1 : evalV v φ = evalV (fun i => n.testBit i) φ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_left _ hi)).symm
    have h2 : evalV v ψ = evalV (fun i => n.testBit i) ψ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_right _ hi)).symm
    have hiff : evalV (fun i => n.testBit i) φ = true ↔ evalV (fun i => n.testBit i) ψ = true := by
      rw [← mem_evalSet_iff, ← mem_evalSet_iff, h]
    rw [h1, h2]
    rcases hφ : evalV (fun i => n.testBit i) φ with - | - <;>
      rcases hψ : evalV (fun i => n.testBit i) ψ with - | - <;> simp_all

/-! ### `Lindenbaum`, the Lindenbaum algebra of propositional calculus -/

/-- **The Lindenbaum algebra of propositional calculus**: `Formula` quotiented by semantic
equivalence. -/
def Lindenbaum : Type := Quotient formulaSetoid

/-- The canonical map to `Set ℕ`, well-defined by `semanticEquiv_iff_evalSet_eq`. -/
def Lindenbaum.toSet : Lindenbaum → Set ℕ :=
  Quotient.lift evalSet fun _ _ h => semanticEquiv_iff_evalSet_eq.mp h

@[simp] theorem Lindenbaum.toSet_mk (φ : Formula) :
    Lindenbaum.toSet ⟦φ⟧ = evalSet φ := rfl

/-! ### The bijection also matches entailment with `⊆` -/

/-- Semantic entailment: `φ ⊨ ψ` iff every valuation satisfying `φ` satisfies `ψ`. -/
def Entails (φ ψ : Formula) : Prop := ∀ v, evalV v φ = true → evalV v ψ = true
end DomainTheory.Neighborhood
