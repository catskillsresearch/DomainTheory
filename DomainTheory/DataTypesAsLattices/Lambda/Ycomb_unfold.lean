/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.omegaComb_app
import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_app


namespace DomainTheory.DataTypesAsLattices


















































/-- **Scott 1976, (2.8) unfolding.** `Y(u) = u(Y(u))`. -/
theorem Ycomb_unfold (u : Pomega) :
    funOf Ycomb u = funOf u (funOf Ycomb u) := by
  calc
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) := Ycomb_app u
    _ = funOf u (funOf (omegaComb u) (omegaComb u)) :=
      omegaComb_app u (omegaComb u)
    _ = funOf u (funOf Ycomb u) := by rw [Ycomb_app]

end DomainTheory.DataTypesAsLattices
