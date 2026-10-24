module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f(fix(g ∘ f))` is a fixed point of `f ∘ g`:
`(f ∘ g)(f(fix(g∘f))) = f((g∘f)(fix(g∘f))) = f(fix(g∘f))`. -/
theorem comp_fixElement_isFixed (f g : ApproximableMap V V) :
    (f.comp g).toElementMap (f.toElementMap (g.comp f).fixElement)
      = f.toElementMap (g.comp f).fixElement := by
  rw [toElementMap_comp]
  -- `g(f(fix(g∘f))) = (g∘f)(fix(g∘f)) = fix(g∘f)`
  have h : g.toElementMap (f.toElementMap (g.comp f).fixElement) = (g.comp f).fixElement := by
    rw [← toElementMap_comp]
    exact toElementMap_fixElement (g.comp f)
  rw [h]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
