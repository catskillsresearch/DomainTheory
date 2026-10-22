module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.sectionX_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.secFixX_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


/-- `!x. τ(x, y)` is a fixed point of the section: `τ(!x.τ(x,y), y) = !x.τ(x,y)`. -/
theorem secFixX_isFixed (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    τ.toElementMap (pair ((secFixX τ).toElementMap y) y) = (secFixX τ).toElementMap y := by
  rw [secFixX_apply, ← sectionX_apply, toElementMap_fixElement]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
