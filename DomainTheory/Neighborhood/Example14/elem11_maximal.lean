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
















theorem elem11_maximal (x : neighborhoodSystem.Element) (h : elem11 ≤ x) : x = elem11 :=
  mem_leaf11_imp x (h leaf11 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.Neighborhood.Example14
