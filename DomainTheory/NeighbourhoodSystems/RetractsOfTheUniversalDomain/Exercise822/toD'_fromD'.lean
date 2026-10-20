module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_mem_cone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_mem_singleton

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

theorem toD'_fromD' (y : D'.Element) : toD' (fromD' y) = y := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (⟨κ, hκ, rfl⟩ | ⟨κ, hκ, rfl⟩)
    · exact (fromD'_mem_cone κ).mp hκ
    · exact (fromD'_mem_singleton κ).mp hκ
  · intro hW
    rcases y.sub hW with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
    · exact Or.inl ⟨κ, (fromD'_mem_cone κ).mpr hW, rfl⟩
    · exact Or.inr ⟨κ, (fromD'_mem_singleton κ).mpr hW, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
