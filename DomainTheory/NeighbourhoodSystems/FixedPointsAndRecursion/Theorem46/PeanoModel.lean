/-ai
A model of Peano's axioms on a type consists of a zero element and a successor operation such that zero is never a successor, the successor is injective, and every subset that contains zero and is closed under the successor contains every element.
ai-/
module


public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

universe u v

namespace DomainTheory.NeighbourhoodSystems

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

end DomainTheory.NeighbourhoodSystems
