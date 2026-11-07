module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_11

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 5.9: commuting endomaps share a least common fixed point;
equal bottoms yield equal least fixed points; in particular fix(f) = fix(f∘f). -/
theorem example_509 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} {f g : ApproximableMap V V},
      f.comp g = g.comp f →
      ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
        ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} {f g : ApproximableMap V V},
      f.comp g = g.comp f →
      f.toElementMap V.bot = g.toElementMap V.bot →
        f.fixElement = g.fixElement) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V),
      f.fixElement = (f.comp f).fixElement) :=
  ⟨@commuting_least_common_fixed, @fixElement_eq_of_commuting_bot, @fixElement_iterTwice⟩

