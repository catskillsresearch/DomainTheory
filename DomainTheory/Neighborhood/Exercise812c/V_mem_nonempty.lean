/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.IntervalPrimrec
import DomainTheory.Neighborhood.Theorem88
import DomainTheory.Neighborhood.Exercise812c.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem







theorem V_mem_nonempty {X : Set ℕ} (hX : V.mem X) : X.Nonempty := by
  obtain ⟨k, m, -, hne⟩ := hX; exact hne

end DomainTheory.Neighborhood
