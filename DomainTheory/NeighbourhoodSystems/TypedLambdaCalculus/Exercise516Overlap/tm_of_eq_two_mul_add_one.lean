module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems



theorem tm_of_eq_two_mul_add_one {x y : ℕ} (h : x = 2 * y + 1) : tm x = !tm y := by
  rw [h, tm_two_mul_add_one]

end DomainTheory.NeighbourhoodSystems.Exercise516
