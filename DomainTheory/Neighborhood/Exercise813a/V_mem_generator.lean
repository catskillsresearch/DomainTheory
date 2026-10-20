/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise813a.Basic
import DomainTheory.Neighborhood.Exercise813a.generator_nonempty
import DomainTheory.Neighborhood.Exercise813a.generator_eq_levelSet


namespace DomainTheory.Neighborhood

open NeighborhoodSystem








theorem V_mem_generator (i : ℕ) : V.mem (generator i) :=
  generator_eq_levelSet i ▸ ⟨i + 1, _, rfl, generator_eq_levelSet i ▸ generator_nonempty i⟩

end DomainTheory.Neighborhood
