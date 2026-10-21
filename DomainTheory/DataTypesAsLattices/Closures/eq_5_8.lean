/-ai
Scott 1976, (5.8). Every set u equals the square pair of its first and second square components.

By extensionality, an even code in the pair simplifies, through the first-component definition, to membership in u, and an odd code does the same through the second component. Conversely, an even number is the left injection of its half after identifying the double with the product by two, and an odd number is the right injection of its predecessor index.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.8).** `u = [[u]₀, [u]₁]`. -/
theorem eq_5_8 (u : Pomega) : squarePair (squareFst u) (squareSnd u) = u := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · simpa [squareFst, hk] using hn
    · simpa [squareSnd, hk] using hm
  · intro hk
    rcases Nat.even_or_odd k with h | h
    · obtain ⟨n, rfl⟩ := h
      have heq : n + n = 2 * n := by omega
      have hn : 2 * n ∈ u := by rwa [← heq]
      exact Or.inl ⟨n, hn, heq⟩
    · obtain ⟨m, rfl⟩ := h
      exact Or.inr ⟨m, hk, rfl⟩

end DomainTheory.DataTypesAsLattices
