module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_append

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `double` preserves the prefix order. -/
theorem double_prefix {σ τ : Str} (h : σ <+: τ) : double σ <+: double τ := by
  obtain ⟨ρ, rfl⟩ := h
  exact ⟨double ρ, (double_append σ ρ).symm⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
