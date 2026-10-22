/-ai
This file gathers and re-exports a model of Peano's axioms and the inductively generated graph relating two such models.
ai-/
module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.PeanoModel

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Graph

@[expose] public section

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
