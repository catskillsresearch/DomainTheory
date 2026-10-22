module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.B_subsystem_C

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822


/-- **`B ⊴ C`** (Exercise 8.22). The projection Scott asks us to notice: the identity inclusion
`B ◁ C`. -/
theorem B_trianglelefteq_C : B ⊴ C :=
  Subsystem.trianglelefteq B_subsystem_C

end Exercise822
end DomainTheory.NeighbourhoodSystems
