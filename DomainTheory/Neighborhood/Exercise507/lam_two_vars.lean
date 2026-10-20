/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise507.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise507

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}




/-- **Two-variable abstraction.** `λx, y. τ` is `curry`, characterised by `(curry g)(x)(y) = g⟨x, y⟩`.
It binds one variable `x` and returns the one-variable function `λy. g⟨x, y⟩`. -/
theorem lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) :=
  toElementMap_curry_apply g x y

end DomainTheory.Neighborhood.Exercise507
