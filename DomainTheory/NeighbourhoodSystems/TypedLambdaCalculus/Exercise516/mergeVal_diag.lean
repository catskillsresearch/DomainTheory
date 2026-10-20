module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}




































/-- The diagonal value: interleaving `(s, σ)` with itself doubles. -/
theorem mergeVal_diag (s : Bool) (σ : Str) : mergeVal σ s σ s = (double σ, s) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp [mergeVal_cons_cons, ih]

end DomainTheory.NeighbourhoodSystems.Exercise516
