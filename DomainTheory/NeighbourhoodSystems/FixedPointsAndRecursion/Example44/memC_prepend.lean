module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.prepend_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- Prepending the bit `b` (or, generally, a prefix `σ`) to a neighbourhood of `C` lands back in
`C`: `σ(τΣ*) = (στ)Σ*` and `σ{τ} = {στ}`. -/
theorem memC_prepend (σ : Str) {X : Set Str} (hX : memC X) : memC (prepend σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prepend_cone σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prepend_singleton σ ρ⟩

end DomainTheory.NeighbourhoodSystems.Example44
