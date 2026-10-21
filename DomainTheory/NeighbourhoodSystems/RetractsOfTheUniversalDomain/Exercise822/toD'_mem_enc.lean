/-ai
The cone of a doubled encoding lies in the forward image of an element of C if and only if the cone of the original string lies in the element.

A cone clause gives the same string by injectivity of cones and of the doubling encoding. A completed clause would make a doubled encoding equal a completed encoding. In the other direction, membership of the cone is the cone clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_ne_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

@[simp] theorem toD'_mem_enc {x : C.Element} (κ : Str) :
    (toD' x).mem (cone (enc κ)) ↔ x.mem (cone κ) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · have hκσ : κ = σ := enc_injective (cone_injective heq)
      rw [hκσ]; exact hσ
    · exact absurd (cone_injective heq) (enc_ne_encC κ σ)
  · intro hx; exact Or.inl ⟨κ, hx, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
