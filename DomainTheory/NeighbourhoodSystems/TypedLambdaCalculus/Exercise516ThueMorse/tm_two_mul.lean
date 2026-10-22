module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- The even recurrence `tm (2n) = tm n` (appending a `0`-digit does not change the parity). -/
theorem tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp only [tm, Nat.bit0_bits n (by omega : n ≠ 0), List.foldr_cons, Bool.false_xor]

end DomainTheory.NeighbourhoodSystems.Exercise516
