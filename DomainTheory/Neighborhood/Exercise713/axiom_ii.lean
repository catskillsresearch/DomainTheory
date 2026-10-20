/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Exercise713.Basic


namespace DomainTheory.Neighborhood.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)



/-- **Axiom (ii).** `INCL` is transitive. -/
theorem axiom_ii {n m k : ℕ} (h1 : I.INCL n m) (h2 : I.INCL m k) : I.INCL n k := I.incl_trans h1 h2

end InclStructure
end DomainTheory.Neighborhood.Exercise713
