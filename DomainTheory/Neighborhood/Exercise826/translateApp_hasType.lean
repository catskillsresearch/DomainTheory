/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise826.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

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

end DomainTheory.Neighborhood
