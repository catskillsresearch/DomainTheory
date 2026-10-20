/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Proposition612
public import DomainTheory.Neighborhood.Exercise628.Basic
public import DomainTheory.Neighborhood.Exercise628.Triangleleftequ2eelementEmbedding
public import DomainTheory.Neighborhood.Exercise628.orderIso_of_embeddings

@[expose] public section


namespace DomainTheory.Neighborhood

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

end DomainTheory.Neighborhood
