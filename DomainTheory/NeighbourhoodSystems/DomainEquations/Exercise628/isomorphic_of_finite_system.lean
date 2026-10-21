/-ai
If two neighbourhood systems are finite and each embeds as a subdomain of the other, then the two systems are isomorphic.

Finiteness of each system gives finiteness of its element domain, and the mutual subdomain embeddings then supply the isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.isomorphic_of_trianglelefteq_both
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.finite_element_of_isFinite

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Exercise 6.28 (Scott 1981, PRG-19; suggested by G. Plotkin).** If `𝒟` and `ℰ` are *finite*
neighbourhood systems with `𝒟 ⊴ ℰ` and `ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. -/
theorem isomorphic_of_finite_system (hD : D.IsFinite) (hE : E.IsFinite)
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  have := finite_element_of_isFinite hD
  have := finite_element_of_isFinite hE
  exact isomorphic_of_trianglelefteq_both h₁ h₂

end DomainTheory.NeighbourhoodSystems
