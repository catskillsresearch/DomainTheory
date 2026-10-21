/-ai
The cone of a string lies in the inverse image of an element of D' if and only if the cone of that string's doubled encoding lies in the element.

A cone clause gives the same string by injectivity of cones. A singleton clause would make a cone equal a singleton. In the other direction, membership of the encoded cone is the cone clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_encC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

@[simp] theorem fromD'_mem_cone {y : D'.Element} (κ : Str) :
    (fromD' y).mem (cone κ) ↔ y.mem (cone (enc κ)) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · have hκσ : κ = σ := cone_injective heq
      rw [hκσ]; exact hσ
    · exact absurd heq (cone_ne_singleton κ σ)
  · intro hy; exact Or.inl ⟨κ, hy, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
