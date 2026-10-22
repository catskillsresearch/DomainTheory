module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_eq_iSupDirected
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_le_of_toElementMap_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_comp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_le_fixElement
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.comp_self_iterElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** In particular `fix(f) = fix(f²)`: the `f²`-chain
`f^{2n}(⊥)` is cofinal in the `f`-chain `fⁿ(⊥)`, so the two least fixed points coincide. -/
theorem fixElement_iterTwice (f : ApproximableMap V V) :
    f.fixElement = (f.comp f).fixElement := by
  apply le_antisymm
  · -- `fix f ⊑ fix f²`: `fⁿ⊥ ⊑ f^{2n}⊥ = (f²)ⁿ⊥ ⊑ fix f²`.
    rw [fixElement_eq_iSupDirected f]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterElem n ≤ f.iterElem (2 * n) := iterElem_mono f (by omega)
      _ = (f.comp f).iterElem n := (comp_self_iterElem f n).symm
      _ ≤ (f.comp f).fixElement := iterElem_le_fixElement (f.comp f) n
  · -- `fix f² ⊑ fix f`: `fix f` is a fixed point of `f²`.
    refine fixElement_le_of_toElementMap_le (f.comp f) (le_of_eq ?_)
    rw [toElementMap_comp, toElementMap_fixElement, toElementMap_fixElement]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
