module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- `σΣ* = Σ*` iff `σ = Λ`. -/
theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil

end DomainTheory.NeighbourhoodSystems.Exercise516
