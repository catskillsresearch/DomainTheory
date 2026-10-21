/-ai
The order isomorphism between elements of C and elements of D' sends an element forward by the encoding map and returns by its inverse. The two composites are the identity. One element of C lies below another exactly when the image does: a cone or singleton of the smaller element is recovered from the corresponding encoded membership of its image, and an encoded cone or completed cone in the smaller image comes from the corresponding cone or singleton of the smaller element.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_toD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_fromD'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **`C ≅ᴰ D'`.** -/
def cdEquiv : C.Element ≃o D'.Element where
  toFun := toD'
  invFun := fromD'
  left_inv := fromD'_toD'
  right_inv := toD'_fromD'
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases x.sub hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
      · exact (toD'_mem_enc σ).mp (h _ ((toD'_mem_enc σ).mpr hX))
      · exact (toD'_mem_encC σ).mp (h _ ((toD'_mem_encC σ).mpr hX))
    · intro h W hW
      rcases hW with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact Or.inl ⟨σ, h _ hσ, rfl⟩
      · exact Or.inr ⟨σ, h _ hσ, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
