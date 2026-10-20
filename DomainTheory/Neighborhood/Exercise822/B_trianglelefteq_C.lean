/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example62
import DomainTheory.Neighborhood.Example44
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise822.Basic
import DomainTheory.Neighborhood.Exercise822.B_subsystem_C


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822



/-- **`B ⊴ C`** (Exercise 8.22). The projection Scott asks us to notice: the identity inclusion
`B ◁ C`. -/
theorem B_trianglelefteq_C : B ⊴ C :=
  Subsystem.trianglelefteq B_subsystem_C

end Exercise822
end DomainTheory.Neighborhood
