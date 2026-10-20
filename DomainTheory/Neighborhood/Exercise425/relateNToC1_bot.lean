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





























/-- `relateNToC1(⊥) = ⊥`. -/
theorem relateNToC1_bot : relateNToC1.toElementMap Example43.N.bot = C1.bot :=
  Example43.constLiftN_bot C1 oneElem

end DomainTheory.Neighborhood.Exercise425
