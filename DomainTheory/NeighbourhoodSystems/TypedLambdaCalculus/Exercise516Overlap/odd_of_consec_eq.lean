/-ai
If the Thue–Morse bit at x equals the bit at x + 1, then x is odd. Equal consecutive symbols only straddle a block boundary, and never an even-odd pair.

Split x into even or odd. An even x is twice some m, and the even-indexed bit differs from its successor. An odd x is the required conclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.tm_two_mul_ne

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems


/-- `tm x = tm (x+1)` forces `x` to be **odd**: equal consecutive symbols only straddle a block
boundary `(2m+1, 2m+2)`, never a block `(2m, 2m+1)`. -/
theorem odd_of_consec_eq {x : ℕ} (h : tm x = tm (x + 1)) : Odd x := by
  rcases Nat.even_or_odd x with ⟨m, hm⟩ | hodd
  · exfalso; rw [hm, ← two_mul] at h; exact tm_two_mul_ne m h
  · exact hodd

end DomainTheory.NeighbourhoodSystems.Exercise516
