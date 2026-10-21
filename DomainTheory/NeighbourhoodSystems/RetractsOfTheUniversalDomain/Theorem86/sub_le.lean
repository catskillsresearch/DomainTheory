/-ai
For every approximable endomap f, the map sub f lies below f.

A relation of sub supplies a neighbourhood containing the input, contained in the output, and related to itself by f. Monotonicity of f narrows the input and then widens the output, giving the relation of f.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}



/-- **`sub f ≤ f`, unconditionally (Scott 1981, PRG-19).** "`X ⊆ Y, f Y ⊆ Z` always implies
`X f Z`" — a bare narrow-input/widen-output monotonicity calculation, needing nothing about `f`. -/
theorem sub_le (f : ApproximableMap E E) : sub f ≤ f := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  have h1 : f.rel X Y := f.mono hYf hXY subset_rfl hX hYE
  exact f.mono h1 subset_rfl hYZ hX hZ

end DomainTheory.NeighbourhoodSystems
