/-ai
The Thue–Morse bit of 2n + 1 is the negation of the Thue–Morse bit of n.

Simplify the definition of the bit, the bits of an odd number, the fold of a cons, and exclusive-or with true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419











/-- The odd recurrence `tm (2n+1) = ¬ tm n` (appending a `1`-digit flips the parity). -/
theorem tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = !tm n := by
  simp only [tm, Nat.bit1_bits n, List.foldr_cons, Bool.true_xor]

end DomainTheory.NeighbourhoodSystems.Exercise516
