module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_11

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

theorem example_509 :
    (∀ {f g : ApproximableMap V V}, f.comp g = g.comp f →
      ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
        ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w) ∧
    (∀ {f g : ApproximableMap V V}, f.comp g = g.comp f →
      f.toElementMap V.bot = g.toElementMap V.bot →
        f.fixElement = g.fixElement) ∧
    (∀ f : ApproximableMap V V, f.fixElement = (f.comp f).fixElement) :=
  ⟨commuting_least_common_fixed, fixElement_eq_of_commuting_bot, fixElement_iterTwice⟩

end
end DomainTheory.NeighbourhoodSystems
