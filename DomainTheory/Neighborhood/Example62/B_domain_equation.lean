/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Exercise319Sum
import DomainTheory.Neighborhood.Example62.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62




































/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `B ≅ B + B`.** Scott's binary-sequence
domain `B` is, as a domain, isomorphic to `B + B`: a sequence is bottom, or begins with `0`, or begins
with `1`, the two non-bottom cases giving the two summands. -/
theorem B_domain_equation : B ≅ᴰ sum B B B_nonempty B_nonempty :=
  ⟨bbEquiv⟩

end Example62
end DomainTheory.Neighborhood
