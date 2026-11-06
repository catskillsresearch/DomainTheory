module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Theorem 4.2: the fix combinator is approximable, least, and an iterate supremum. -/
theorem theorem_42 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (φ : (funSpace V V).Element),
      (toApproxMap φ).toElementMap ((fixMap V).toElementMap φ) = (fixMap V).toElementMap φ) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) {z : V.Element},
      (toApproxMap φ).toElementMap z ≤ z → (fixMap V).toElementMap φ ≤ z) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (φ : (funSpace V V).Element),
      (fixMap V).toElementMap φ =
        NeighborhoodSystem.iSupDirected ((toApproxMap φ).iterElem)
          (fun i j => ⟨max i j, iterElem_mono _ (le_max_left i j),
            iterElem_mono _ (le_max_right i j)⟩)) :=
  ⟨@toElementMap_fixMap, @fixMap_least, @fixMap_eq_iSup⟩

end DomainTheory.NeighbourhoodSystems
