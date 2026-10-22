module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_eq_iterate
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_eq_iSupDirected
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_le_of_toElementMap_le
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.iterElem_le_fixElement

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.11(iii) (Scott 1981, PRG-19).** `fix` is *uniform*: if `h(⊥) = ⊥` and
`h ∘ f₀ = f₁ ∘ h`, then `h(fix f₀) = fix f₁`. -/
theorem fixElement_uniform {β γ : Type*} {W₀ : NeighborhoodSystem β} {W₁ : NeighborhoodSystem γ}
    (f₀ : ApproximableMap W₀ W₀) (f₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁)
    (hbot : h.toElementMap W₀.bot = W₁.bot)
    (hintw : ∀ x, h.toElementMap (f₀.toElementMap x) = f₁.toElementMap (h.toElementMap x)) :
    h.toElementMap f₀.fixElement = f₁.fixElement := by
  -- `h` carries the `n`-th approximant of `f₀` to that of `f₁`.
  have hiter : ∀ n, h.toElementMap (f₀.iterElem n) = f₁.iterElem n := by
    intro n
    rw [iterElem_eq_iterate f₀ n, iterElem_eq_iterate f₁ n]
    induction n with
    | zero => simpa using hbot
    | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply, hintw, ih]
  apply le_antisymm
  · -- `h(fix f₀) = ⊔ₙ h(f₀ⁿ(⊥)) = ⊔ₙ f₁ⁿ(⊥) ⊑ fix f₁`.
    rw [fixElement_eq_iSupDirected f₀, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    rw [hiter n]
    exact iterElem_le_fixElement f₁ n
  · -- `h(fix f₀)` is a fixed point of `f₁`, so `fix f₁ ⊑ h(fix f₀)` by minimality.
    have hfp : f₁.toElementMap (h.toElementMap f₀.fixElement) = h.toElementMap f₀.fixElement := by
      rw [← hintw f₀.fixElement, toElementMap_fixElement]
    exact fixElement_le_of_toElementMap_le f₁ (le_of_eq hfp)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
