/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise813a.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem








theorem generator_nonempty (i : ℕ) : (generator i).Nonempty := ⟨2 ^ i, by simp⟩

end DomainTheory.Neighborhood
