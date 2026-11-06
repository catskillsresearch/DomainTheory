module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.eval

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Theorem 3.11: evaluation is an approximable map satisfying eval(f, x) = f(x). -/
theorem theorem_3_11 :
    ∀ {β γ : Type*} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
      (φ : (funSpace V₁ V₂).Element) (x : V₁.Element),
      (evalMap V₁ V₂).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x :=
  @evalMap_apply

end DomainTheory.NeighbourhoodSystems
