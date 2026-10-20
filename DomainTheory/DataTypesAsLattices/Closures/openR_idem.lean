/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.openR_app
import DomainTheory.DataTypesAsLattices.Closures.openR_expansive


namespace DomainTheory.DataTypesAsLattices



































theorem openR_idem (u : Pomega) :
    funOf openR (funOf openR u) = funOf openR u := by
  apply subset_antisymm
  · intro m hm
    rw [openR_app] at hm ⊢
    obtain ⟨n, hn, hnu⟩ := hm
    rw [openR_app] at hnu
    obtain ⟨k, hk, hku⟩ := hnu
    exact ⟨k, subset_trans hk hn, hku⟩
  · exact openR_expansive (funOf openR u)

end DomainTheory.DataTypesAsLattices
