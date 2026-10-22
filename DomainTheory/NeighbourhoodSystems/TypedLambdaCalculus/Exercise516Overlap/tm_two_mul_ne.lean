module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_two_mul
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_two_mul_add_one
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems


/-- An even-indexed symbol differs from its successor: `tm (2x) ≠ tm (2x+1)`. -/
theorem tm_two_mul_ne (x : ℕ) : tm (2 * x) ≠ tm (2 * x + 1) := by
  rw [tm_two_mul, tm_two_mul_add_one]
  cases tm x <;> simp

end DomainTheory.NeighbourhoodSystems.Exercise516
