module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.funSpaceEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Theorem 3.10: every ideal element of a function space is fixed by a unique
    approximable mapping, via the order isomorphism with maps. -/
theorem theorem_3_10 :
    ∀ {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β),
      Nonempty ((funSpace V₀ V₁).Element ≃o ApproximableMap V₀ V₁) :=
  fun {_ _} V₀ V₁ => ⟨funSpaceEquiv V₀ V₁⟩

end DomainTheory.NeighbourhoodSystems
