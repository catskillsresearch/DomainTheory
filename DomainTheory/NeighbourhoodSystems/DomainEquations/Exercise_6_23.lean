module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.exprDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB SmashProduct Exercise619

/-- Scott's Exercise 6.23: the descending approximable map is below any algebra homomorphism. -/
theorem example_623 {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))
    (g : AlgHom (ExpAlg N hN) B) :
    descMap hN B ≤ g.hom.1 :=
  @descMap_le_algHom _ hN B g

end DomainTheory.NeighbourhoodSystems
