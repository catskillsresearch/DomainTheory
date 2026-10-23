module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.generatedBy_biUnion_affine

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem generatedBy_levelSet (k m : ℕ) : GeneratedBy generator (levelSet k m) := by
  rw [levelSet.eq_biUnion]
  exact generatedBy_biUnion_affine k _ fun ℓ hℓ => (Finset.mem_filter.mp hℓ).1 |> Finset.mem_range.mp

end DomainTheory.NeighbourhoodSystems
