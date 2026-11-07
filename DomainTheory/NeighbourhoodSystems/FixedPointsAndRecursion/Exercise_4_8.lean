module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixInduction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
open NeighborhoodSystem ApproximableMap

theorem example_408 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f a b : ApproximableMap V V),
      a.toElementMap V.bot = b.toElementMap V.bot →
        f.comp a = a.comp f → f.comp b = b.comp f →
          a.toElementMap f.fixElement = b.toElementMap f.fixElement) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      (P : V.Element → Prop),
      P V.bot →
        (∀ x, P x → P (f.toElementMap x)) →
          (∀ (s : ℕ → V.Element) (hmono : Monotone s),
            (∀ n, P (s n)) → P (supChain s hmono)) →
            P f.fixElement) :=
  ⟨@fix_induction_eq, @fix_induction⟩
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
