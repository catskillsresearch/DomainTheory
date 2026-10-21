/-ai
The inverse map is a left inverse of the forward map from elements of C to elements of D'.

Compare elements by membership. A cone or singleton in the inverse image of the forward image comes from the corresponding membership law for the forward map. Conversely, the subelement law writes a neighbourhood as a cone or a singleton, and the corresponding membership law puts it back into the composite.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
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

theorem fromD'_toD' (x : C.Element) : fromD' (toD' x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · exact (toD'_mem_enc σ).mp hσ
    · exact (toD'_mem_encC σ).mp hσ
  · intro hX
    rcases x.sub hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
    · exact Or.inl ⟨σ, (toD'_mem_enc σ).mpr hX, rfl⟩
    · exact Or.inr ⟨σ, (toD'_mem_encC σ).mpr hX, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
