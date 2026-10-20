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































theorem predSet_succSet (x : Pomega) : predSet (succSet x) = x := by
  ext k
  constructor
  · intro ⟨n, hn, heq⟩
    exact (Nat.succ_injective heq) ▸ hn
  · intro hk
    exact ⟨k, hk, rfl⟩

end DomainTheory.DataTypesAsLattices
