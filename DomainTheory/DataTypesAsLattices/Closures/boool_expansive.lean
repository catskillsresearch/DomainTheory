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



































theorem boool_expansive (u : Pomega) :
    u ⊆ condSet u (ofNat 0) (succSet topElem) := by
  intro k hk
  cases k with
  | zero => exact Or.inl ⟨rfl, hk⟩
  | succ k => exact Or.inr ⟨⟨k, Set.mem_univ k, rfl⟩, ⟨k, hk⟩⟩

end DomainTheory.DataTypesAsLattices
