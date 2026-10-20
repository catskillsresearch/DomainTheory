/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise507.Basic


namespace DomainTheory.Neighborhood.Exercise507

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}




/-- The two encodings are mutually inverse: uncurrying the two-variable abstraction returns the
original two-variable function. -/
theorem uncurry_lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g :=
  uncurry_curry g

end DomainTheory.Neighborhood.Exercise507
