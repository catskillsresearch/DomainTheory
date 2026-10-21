/-ai
C is domain-isomorphic to the image neighbourhood system D'.

The isomorphism is the order equivalence between their elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822


theorem C_isomorphic_D' : C ≅ᴰ D' := ⟨cdEquiv⟩

end Exercise822
end DomainTheory.NeighbourhoodSystems
