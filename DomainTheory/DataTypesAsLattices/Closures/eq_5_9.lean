/-ai
Scott 1976, (5.9) and (5.10). The first square projection of a square pair of x and y is x.

By extensionality, a left code in the first projection has index equal to the element and therefore lies in x, while a right code is numerically impossible. Conversely, each member of x is the left code of itself.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






/-- **Scott 1976, (5.9)–(5.10).** -/
theorem eq_5_9 (x y : Pomega) : squareFst (squarePair x y) = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, h⟩ | ⟨m, _, h⟩
    · have : k = n := by omega
      simpa [this] using hk
    · omega
  · intro hn
    exact Or.inl ⟨n, hn, rfl⟩

end DomainTheory.DataTypesAsLattices
