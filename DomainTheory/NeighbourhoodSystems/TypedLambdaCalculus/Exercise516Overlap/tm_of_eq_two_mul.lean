module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_two_mul
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems


theorem tm_of_eq_two_mul {x y : ℕ} (h : x = 2 * y) : tm x = tm y := by
  rw [h, tm_two_mul]

end DomainTheory.NeighbourhoodSystems.Exercise516
