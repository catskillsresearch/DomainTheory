/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Continuous
import DomainTheory.DataTypesAsLattices.Graph.Basic
import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_right
import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_left


namespace DomainTheory.DataTypesAsLattices




/-- **Scott 1976, (μ).** Application is monotone in both arguments. -/
theorem mu_law {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y :=
  subset_trans (funOf_monotone_left hu x) (funOf_monotone_right v hx)

end DomainTheory.DataTypesAsLattices
