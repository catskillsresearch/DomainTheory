/-ai
If the element domains of two neighbourhood systems are finite and each system embeds as a subdomain of the other, then the systems are isomorphic.

Each embedding supplies an order embedding of element domains, and those two embeddings form an order isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.Triangleleftequ2eelementEmbedding
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.orderIso_of_embeddings

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Exercise 6.28 (core).** If `|D|` and `|E|` are finite and `D ⊴ E ⊴ D`, then `D ≅ᴰ E`.
The two `⊴`s give mutual order embeddings of the (finite) element domains, and
`orderIso_of_embeddings` upgrades them to an isomorphism. -/
theorem isomorphic_of_trianglelefteq_both [Finite D.Element] [Finite E.Element]
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  obtain ⟨f⟩ := h₁.elementEmbedding
  obtain ⟨g⟩ := h₂.elementEmbedding
  exact orderIso_of_embeddings f g

end DomainTheory.NeighbourhoodSystems
