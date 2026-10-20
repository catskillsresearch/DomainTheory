/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise421.Basic


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414



theorem leOp_monotone : Monotone leOp := by
  intro u v huv p hp
  rcases hp with hp | ⟨m, hm, hpm⟩
  · exact Or.inl hp
  · exact Or.inr ⟨m, huv hm, hpm⟩

end DomainTheory.Neighborhood.Exercise421
