module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.projPairSubdomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- Scott's Lemma 6.15: a projection pair yields a domain embedding. -/
theorem lemma_615 :
    ∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
      (i : ApproximableMap D E) (j : ApproximableMap E D),
      j.comp i = idMap D → i.comp j ≤ idMap E → D ⊴ E :=
  @trianglelefteq_of_projectionPair

end DomainTheory.NeighbourhoodSystems
