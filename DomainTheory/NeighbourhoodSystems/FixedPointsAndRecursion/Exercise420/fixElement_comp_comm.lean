/-ai
For approximable endomaps f and g of a domain, the least fixed point of f composed with g equals f applied to the least fixed point of g composed with f.

The right-hand side is a fixed point of f composed with g, so the least fixed point lies below it. In the other direction, the same fact with the maps exchanged places the least fixed point of g composed with f below g applied to the least fixed point of f composed with g. Monotonicity of f, the composition law, and the fixed-point equation of f composed with g then place the right-hand side below the left-hand side.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise420.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise420.comp_fixElement_isFixed

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.20 (Scott 1981, PRG-19).** `fix(f ∘ g) = f(fix(g ∘ f))`. -/
theorem fixElement_comp_comm (f g : ApproximableMap V V) :
    (f.comp g).fixElement = f.toElementMap (g.comp f).fixElement := by
  apply le_antisymm
  · -- `fix(f∘g) ⊑ f(fix(g∘f))` since the latter is a (pre-)fixed point of `f∘g`.
    exact fixElement_le_of_toElementMap_le (f.comp g)
      (le_of_eq (comp_fixElement_isFixed f g))
  · -- `f(fix(g∘f)) ⊑ fix(f∘g)`. First, `fix(g∘f) ⊑ g(fix(f∘g))`.
    have hga : (g.comp f).fixElement ≤ g.toElementMap (f.comp g).fixElement := by
      apply fixElement_le_of_toElementMap_le (g.comp f)
      have : (g.comp f).toElementMap (g.toElementMap (f.comp g).fixElement)
          = g.toElementMap (f.comp g).fixElement := comp_fixElement_isFixed g f
      exact le_of_eq this
    -- apply `f` and use `f(g(fix(f∘g))) = (f∘g)(fix(f∘g)) = fix(f∘g)`.
    calc f.toElementMap (g.comp f).fixElement
        ≤ f.toElementMap (g.toElementMap (f.comp g).fixElement) := f.toElementMap_mono hga
      _ = (f.comp g).toElementMap (f.comp g).fixElement := by rw [toElementMap_comp]
      _ = (f.comp g).fixElement := toElementMap_fixElement (f.comp g)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
