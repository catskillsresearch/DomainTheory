module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sSupMaps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Theorem 3.13: approximation is pointwise, boundedness of maps is pointwise
    boundedness of values, and the supremum of maps acts pointwise. -/
theorem theorem_3_13 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f g : ApproximableMap V₀ V₁),
      f ≤ g ↔ ∀ x, f.toElementMap x ≤ g.toElementMap x) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (F : Set (ApproximableMap V₀ V₁)),
      MapsBounded F ↔ PointwiseBounded F) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F) (x : V₀.Element),
      (sSupMaps F hF).toElementMap x =
        V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x)) :=
  ⟨@le_iff_toElementMap_le, @mapsBounded_iff_pointwiseBounded, @toElementMap_sSupMaps⟩

end DomainTheory.NeighbourhoodSystems
