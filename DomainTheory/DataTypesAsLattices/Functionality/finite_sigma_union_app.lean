/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag
import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_union_fresh
import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_fresh_app


namespace DomainTheory.DataTypesAsLattices






























theorem finite_sigma_union_app (p q m : ℕ) :
    funOf
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) ∪ {pair (max p q + 1) (m + 1)} := by
  rw [eq_2_9, normalized_finite_fresh_app, sigmaJ_app,
    sigmaJ_union_fresh (fun k => Z_finite_no_tag p q m k)]

end DomainTheory.DataTypesAsLattices
