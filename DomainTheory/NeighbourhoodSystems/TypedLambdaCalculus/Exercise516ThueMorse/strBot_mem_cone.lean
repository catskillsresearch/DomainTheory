module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
















/-- `(strBot τ)` has the cone of `σ` as a neighbourhood iff `σ` is a prefix of `τ`. -/
theorem strBot_mem_cone {σ τ : Str} : (strBot τ).mem (cone σ) ↔ σ <+: τ := by
  rw [strBot, mem_principal]
  exact ⟨fun h => cone_subset_cone.mp h.2, fun h => ⟨memC_cone σ, cone_subset_cone.mpr h⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
