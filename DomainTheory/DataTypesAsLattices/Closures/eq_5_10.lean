/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices






theorem eq_5_10 (x y : Pomega) : squareSnd (squarePair x y) = y := by
  ext m
  constructor
  · intro hm
    rcases hm with ⟨n, _, h⟩ | ⟨k, hk, h⟩
    · omega
    · have : k = m := by omega
      simpa [this] using hk
  · intro hm
    exact Or.inr ⟨m, hm, rfl⟩

end DomainTheory.DataTypesAsLattices
