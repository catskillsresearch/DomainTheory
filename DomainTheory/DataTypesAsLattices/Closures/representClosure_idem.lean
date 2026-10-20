/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























theorem representClosure_idem {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    representClosure D (representClosure D x) = representClosure D x := by
  apply subset_antisymm
  · intro m hm
    exact hm.trans (by
      apply sSup_le
      intro q hq
      obtain ⟨n, hn, rfl⟩ := hq
      exact hn)
  · exact representClosure_expansive D (representClosure D x)

end DomainTheory.DataTypesAsLattices
