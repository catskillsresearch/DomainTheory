module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_ne_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_enc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

@[simp] theorem toD'_mem_encC {x : C.Element} (κ : Str) :
    (toD' x).mem (cone (encC κ)) ↔ x.mem ({κ} : Set Str) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · exact absurd (cone_injective heq).symm (enc_ne_encC σ κ)
    · have hκσ : κ = σ := encC_injective (cone_injective heq)
      rw [hκσ]; exact hσ
  · intro hx; exact Or.inr ⟨κ, hx, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
