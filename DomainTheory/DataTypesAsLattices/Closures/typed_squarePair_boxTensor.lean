/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
import DomainTheory.DataTypesAsLattices.Closures.boxTensor_app
import DomainTheory.DataTypesAsLattices.Closures.squarePair_inj


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.4.** A boxed pair is typed
for `⊠` iff its components are typed. -/
theorem typed_squarePair_boxTensor (a b x y : Pomega) :
    typed (squarePair x y) (boxTensor a b) ↔ typed x a ∧ typed y b := by
  constructor
  · intro h
    have : squarePair x y = squarePair (funOf a x) (funOf b y) := by
      simpa [typed, boxTensor_app, eq_5_9, eq_5_10] using h
    exact squarePair_inj this
  · intro ⟨hx, hy⟩
    rw [typed, boxTensor_app, eq_5_9, eq_5_10, ← hx, ← hy]

end DomainTheory.DataTypesAsLattices
