module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.C_isomorphic_Du27

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822


/-- **`C ⊴ B`.** The nontrivial half of Exercise 8.22: `C` (finite-or-infinite binary sequences)
embeds as a subdomain of `B` (infinite binary sequences) via the bit-doubling re-encoding
`enc`/`encC` and the image subsystem `D' ◁ B`. -/
theorem C_trianglelefteq_B : C ⊴ B := ⟨D', D'_subsystem_B, C_isomorphic_D'⟩

end Exercise822
end DomainTheory.NeighbourhoodSystems
