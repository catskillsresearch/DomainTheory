/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Tactic

/-!
# Lecture IV (§4) — Definition 4.5 and Theorem 4.6: models of Peano's Axioms

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981),
Lecture IV, *Fixed points and recursion*, pages 65–66.

* **Definition 4.5** — a *model for Peano's Axioms* is a structured set `⟨N, 0, ⁺⟩` (a type `N`
  with a distinguished element `0 : N` and a unary `successor` `⁺ : N → N`) satisfying:
  (i) `0 ≠ n⁺` for all `n`; (ii) `n⁺ = m⁺ ⟹ n = m` (the successor is injective);
  (iii) **induction**: whenever `x ⊆ N` has `0 ∈ x` and `x⁺ ⊆ x`, then `x = N`.
  We package this as `PeanoModel`, stating (iii) in the equivalent point form
  `0 ∈ s → (∀ n ∈ s, n⁺ ∈ s) → ∀ n, n ∈ s` (`x⁺ ⊆ x` is `∀ n ∈ x, n⁺ ∈ x`; `x = N` is
  `∀ n, n ∈ x`).

* **Theorem 4.6** — *all models of Peano's Axioms are isomorphic* (`peano_models_isomorphic`).
  Scott's proof is an application of the **Fixed-point Theorem 4.1**: between models
  `⟨N,0,⁺⟩` and `⟨M,□,#⟩` he forms, on the powerset domain `P(N × M)`, the approximable
  operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` and takes its **least fixed point** `r`.

  We realize that least fixed point directly as the inductively generated relation `Graph`
  (the least set of pairs containing `(0,□)` and closed under `(n,m) ↦ (n⁺,m#)` — exactly the
  least fixed point of Scott's monotone operator, by Theorem 4.1). Scott's two facts
  (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#` are the two constructors. We then show `Graph` is a
  one-one correspondence: functionality + totality on the right (`exists_unique_right`, by
  induction 4.5(iii) using 4.5(i)/(ii) to invert the generating rules) and, by the symmetry of
  the construction, on the left (`exists_unique_left`). This yields the structure-preserving
  bijection `e : N ≃ M` with `e 0 = □` and `e (n⁺) = (e n)#`.

All of the *content* (the relation `Graph`, the uniqueness lemmas) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); only the packaging of the bijection `N ≃ M` from the
functional-and-total relation pulls `Classical.choice`, exactly as a Dedekind/recursion theorem
must.
-/

namespace DomainTheory.Neighborhood

universe u v

/-- **Definition 4.5 (Scott 1981, PRG-19).** A *model for Peano's Axioms*: a type `N` with a
distinguished element `zero` and a unary `succ`essor, satisfying

* (i)   `zero ≠ succ n` for all `n`                       (`zero_ne_succ`);
* (ii)  `succ` is injective (`n⁺ = m⁺ ⟹ n = m`)          (`succ_injective`);
* (iii) **mathematical induction**: any `s ⊆ N` with `zero ∈ s` and closed under `succ`
        (`∀ n ∈ s, succ n ∈ s`, i.e. Scott's `x⁺ ⊆ x`) is all of `N`
        (`∀ n, n ∈ s`, i.e. Scott's `x = N`)              (`induction`). -/
structure PeanoModel (N : Type u) where
  /-- The distinguished zero `0 ∈ N`. -/
  zero : N
  /-- The unary successor `⁺ : N → N`. -/
  succ : N → N
  /-- **4.5(i)** `0 ≠ n⁺`. -/
  zero_ne_succ : ∀ n, zero ≠ succ n
  /-- **4.5(ii)** the successor is one-one. -/
  succ_injective : Function.Injective succ
  /-- **4.5(iii)** the induction principle (point form of `x⁺ ⊆ x ⟹ x = N`). -/
  induction : ∀ (s : Set N), zero ∈ s → (∀ n ∈ s, succ n ∈ s) → ∀ n, n ∈ s

namespace PeanoModel

variable {M : Type u} {N : Type v}

/-- Scott's least fixed point `r ⊆ N × M`, realized as the inductively generated relation: the
least relation containing `(0, □)` and closed under `(n, m) ↦ (n⁺, m#)`. The two constructors are
Scott's facts (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#`. By Theorem 4.1 this *is* the least fixed
point of the approximable operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` on `P(N × M)`. -/
inductive Graph (P : PeanoModel M) (Q : PeanoModel N) : M → N → Prop
  | base : Graph P Q P.zero Q.zero
  | step : ∀ {m n}, Graph P Q m n → Graph P Q (P.succ m) (Q.succ n)
end PeanoModel
end DomainTheory.Neighborhood
