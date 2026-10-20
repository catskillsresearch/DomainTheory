module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- **Any two `NeighborhoodSystem`s with `Unique` element posets are isomorphic.** Both sides are
order-isomorphic to the one-point poset `PUnit`, so the isomorphism is forced. -/
def isoOfUnique (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    [Unique V₀.Element] [Unique V₁.Element] : V₀.Element ≃o V₁.Element where
  toFun _ := default
  invFun _ := default
  left_inv x := (Unique.eq_default x).symm
  right_inv y := (Unique.eq_default y).symm
  map_rel_iff' := by
    intro a b
    exact iff_of_true (le_refl _) (le_of_eq (Subsingleton.elim a b))

end DomainTheory.NeighbourhoodSystems
