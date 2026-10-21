/-ai
The singleton of a string is contained in a cone if and only if the cone's string is a prefix of that string.

Singleton inclusion rewrites as membership of the string in the cone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- `{τ} ⊆ σΣ*` iff `σ` is an initial segment of `τ`. -/
theorem singleton_subset_cone {σ τ : Str} : ({τ} : Set Str) ⊆ cone σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_cone]

end DomainTheory.NeighbourhoodSystems.Example44
