module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.regularLanguage

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 7.22: embedding, associativity, and stream-arrow idempotence. -/
theorem example_722 :
    (∀ (σ τ : List Bool), emb (σ ++ τ) = mulElem (emb σ) (emb τ)) ∧
    (∀ (x y z : Ssys.Element), mulElem (mulElem x y) z = mulElem x (mulElem y z)) ∧
    (∀ (σ : List Bool), mulElem (streamArrow σ) (streamArrow σ) = streamArrow σ) :=
  ⟨@emb_mul, ⟨@mulElem_assoc, @streamArrow_mul_self⟩⟩
end


