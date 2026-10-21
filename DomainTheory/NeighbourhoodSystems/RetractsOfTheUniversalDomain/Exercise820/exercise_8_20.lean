/-ai
For any domain D, D is a retract of the product of D with itself, and D is a retract of the function space from D to D.

The two conjuncts are the specializations of the product retract and the constant-function retract.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.D_trianglelefteq_prod
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.D_trianglelefteq_funSpace

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u


variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20.** For any domain `D`, `D ⊴ D×D` and `D ⊴ D→D` (unconditionally — no hypotheses
needed, unlike Exercise 8.19). See the module docstring for the discussion of computability and
multiplicity of projection pairs that Scott also asks about. -/
theorem exercise_8_20 : D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  ⟨D_trianglelefteq_prod D, D_trianglelefteq_funSpace D⟩

end DomainTheory.NeighbourhoodSystems
