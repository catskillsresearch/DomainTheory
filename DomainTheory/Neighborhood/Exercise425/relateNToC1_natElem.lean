/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise425.Basic


namespace DomainTheory.Neighborhood.Exercise425

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap





























/-- `relateNToC1(n̂) = 1ⁿ`. -/
theorem relateNToC1_natElem (n : ℕ) :
    relateNToC1.toElementMap (Example43.natElem n) = oneElem n :=
  Example43.constLiftN_natElem C1 oneElem n

end DomainTheory.Neighborhood.Exercise425
