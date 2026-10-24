module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap
/- concordance: source L2325 EXERCISE 4.20 fix of a composite -/
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
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

end DomainTheory.NeighbourhoodSystems
end
