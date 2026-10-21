/-ai
If a neighbourhood system embeds as a subdomain of another, then there is an order embedding of the element domain of the first into the element domain of the second.

Unfold the embedding into a subdomain together with an order isomorphism onto that subdomain, and compose the isomorphism, read as an order embedding, with the element embedding of the projection pair carried by the subdomain relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.Basic

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **`D ⊴ E` yields an order embedding `|D| ↪o |E|`.** Unfold `⊴` to an iso `|D| ≅o |D'|` onto a
subdomain `D' ◁ E`, turn `D' ◁ E` into Proposition 6.12's projection pair, and compose its
injection embedding with the iso. Choice-free. -/
theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩

end DomainTheory.NeighbourhoodSystems
