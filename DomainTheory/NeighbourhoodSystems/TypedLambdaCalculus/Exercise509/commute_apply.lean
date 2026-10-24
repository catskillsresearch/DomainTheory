module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Commutation `f ∘ g = g ∘ f` read elementwise: `f(g(x)) = g(f(x))`. -/
theorem commute_apply {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) (x : V.Element) :
    f.toElementMap (g.toElementMap x) = g.toElementMap (f.toElementMap x) := by
  have h1 : (f.comp g).toElementMap x = (g.comp f).toElementMap x := by rw [hcomm]
  rwa [toElementMap_comp, toElementMap_comp] at h1

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
