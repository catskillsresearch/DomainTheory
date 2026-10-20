/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88a
import DomainTheory.Neighborhood.Example15
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.PalomarExamples.Basic


namespace DomainTheory.Neighborhood.Example15

/-- **New corollary for Example 1.5.** The finite powerset system is countable, so the first
sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem P4_embeds : neighborhoodSystem ⊴ U :=
  theorem_8_8 neighborhoodSystem

end DomainTheory.Neighborhood.Example15
