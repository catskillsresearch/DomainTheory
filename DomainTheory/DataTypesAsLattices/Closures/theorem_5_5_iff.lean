/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
import DomainTheory.DataTypesAsLattices.Closures.eq_5_17
import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_eq
import DomainTheory.DataTypesAsLattices.Closures.Vapply_right_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.18).** `a = V(a)` iff `a` is a closure. -/
theorem theorem_5_5_iff (a : Pomega) :
    IsClosure a ↔ funOf Vcomb a = a := by
  constructor
  · intro ha
    rw [Vcomb_app]
    have : graph (fun x => Vapply a x) = graph (funOf a) :=
      graph_ext fun x => eq_5_18_eq ha x
    exact this.trans (retract_isGraph ha.2)
  · intro h
    have ha : a = graph (fun x => Vapply a x) :=
      h.symm.trans (Vcomb_app a)
    have happ : ∀ x, funOf a x = Vapply a x := by
      intro x
      conv_lhs => rw [ha]
      exact beta (Vapply_right_isScottContinuous a) x
    constructor
    · intro p hp
      rcases hp with ⟨n, m, rfl, hm⟩
      have : pair n m ∈ graph (fun x => Vapply a x) :=
        ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
      rwa [← ha] at this
    · have : graph (fun x => Vapply a x) =
          graph (fun x => funOf a (funOf a x)) :=
        graph_ext fun x =>
          calc Vapply a x
              = Vapply a (Vapply a x) := (eq_5_17 a x).symm
            _ = funOf a (Vapply a x) := (happ (Vapply a x)).symm
            _ = funOf a (funOf a x) := by rw [← happ x]
      exact ha.trans this

end DomainTheory.DataTypesAsLattices
