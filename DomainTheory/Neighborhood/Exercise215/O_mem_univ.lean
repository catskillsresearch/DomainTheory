/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Exercise215.Basic


namespace DomainTheory.Neighborhood.Exercise215

open DomainTheory.Neighborhood NeighborhoodSystem








theorem O_mem_univ : O.mem (Set.univ : Set (Fin 1)) := Or.inl rfl

end DomainTheory.Neighborhood.Exercise215
