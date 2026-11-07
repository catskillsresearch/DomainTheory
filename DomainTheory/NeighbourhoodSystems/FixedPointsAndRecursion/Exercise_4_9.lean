module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.bigPsi

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

theorem example_409 :
    (∀ {α : Type*} (V : NeighborhoodSystem α)
      (θ : (funSpace (funSpace V V) V).Element) (f : (funSpace V V).Element),
      (toApproxMap ((bigPsi V).toElementMap θ)).toElementMap f
        = (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α),
      (bigPsi V).toElementMap (toFilter (fixMap V)) = toFilter (fixMap V)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α)
      (θ : (funSpace (funSpace V V) V).Element),
      (bigPsi V).toElementMap θ ≤ θ → toFilter (fixMap V) ≤ θ) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α),
      toFilter (fixMap V) = (bigPsi V).fixElement) :=
  ⟨@bigPsi_apply, @bigPsi_fix, @bigPsi_least, @fix_eq_fixElement_bigPsi⟩

end DomainTheory.NeighbourhoodSystems
