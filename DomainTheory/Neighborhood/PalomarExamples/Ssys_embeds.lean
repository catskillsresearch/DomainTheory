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



namespace DomainTheory.Neighborhood.Exercise722


/-- **New corollary for Exercise 7.22.** Countability is `Ssys_countable` (via `SExpr`), so the
first sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem Ssys_embeds : Ssys ⊴ U :=
  theorem_8_8 Ssys

end DomainTheory.Neighborhood.Exercise722
