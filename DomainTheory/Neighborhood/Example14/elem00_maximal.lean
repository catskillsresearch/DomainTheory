/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Example14.Basic


namespace DomainTheory.Neighborhood.Example14













































namespace neighborhoodSystem

open NeighborhoodSystem
















theorem elem00_maximal (x : neighborhoodSystem.Element) (h : elem00 ≤ x) : x = elem00 :=
  mem_leaf00_imp x (h leaf00 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.Neighborhood.Example14
