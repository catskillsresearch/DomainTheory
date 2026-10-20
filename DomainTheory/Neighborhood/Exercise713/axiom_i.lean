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



/-- **Axiom (i).** `INCL` is reflexive. -/
theorem axiom_i (n : ℕ) : I.INCL n n := I.incl_refl n

end InclStructure
end DomainTheory.Neighborhood.Exercise713
