module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.finiteEmbedCancel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

theorem example_628 :
    (∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β},
      D.IsFinite → E.IsFinite → D ⊴ E → E ⊴ D → D ≅ᴰ E) ∧
    (∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
      [Finite D.Element] [Finite E.Element],
      D ⊴ E → E ⊴ D → D ≅ᴰ E) :=
  ⟨@isomorphic_of_finite_system, @isomorphic_of_trianglelefteq_both⟩

end DomainTheory.NeighbourhoodSystems
