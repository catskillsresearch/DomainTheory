/-ai
If b composed with f composed with a equals f, and a fixes an element x, then b fixes the value of f at x.

Rewrite the right-hand side by the sandwich hypothesis and by the two composition laws for element maps, and use that a fixes x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap





universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **The matching claim for application**: if `f` already "has the right type" (`f = b∘f∘a`) and
`x` already "has type `D_a`" (`a(x) = x`), then `f(x)` already "has type `D_b`" (`b(f(x)) = f(x)`).
Together with `translateAbs_sandwich`, this is the type-soundness invariant that both the
`λ`-abstraction and application clauses of the typed-to-untyped translation preserve. -/
theorem translateApp_hasType {a b f : ApproximableMap E E} (hsandwich : b.comp (f.comp a) = f)
    {x : E.Element} (hx : a.toElementMap x = x) :
    b.toElementMap (f.toElementMap x) = f.toElementMap x := by
  conv_rhs => rw [← hsandwich, toElementMap_comp, toElementMap_comp, hx]

end DomainTheory.NeighbourhoodSystems
