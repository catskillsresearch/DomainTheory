/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Exercise214.Basic
import DomainTheory.Neighborhood.Exercise214.phi_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 2.7 defining equation: `e(↑X) = ↑φ(X)`.** -/
theorem phi_spec (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    e (V₀.principal hX) = V₁.principal (phi_mem e hX) :=
  Classical.choose_spec (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

end DomainTheory.Neighborhood
