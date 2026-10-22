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
