module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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
