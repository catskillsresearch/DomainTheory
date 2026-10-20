/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic


namespace Domain.Recursive

















































































































































































































































open DomainTheory.Neighborhood Exercise722





































theorem primrec_codeBound : Nat.Primrec codeBound := by
  have hstep : Nat.Primrec (fun w => Nat.pair 1 w.unpair.2 + 1) :=
    primrec_add₂ (Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.right)
      (Nat.Primrec.const 1)
  have haux : ∀ n, Nat.rec (motive := fun _ => ℕ) 1
      (fun y IH => Nat.pair 1 (Nat.pair y IH).unpair.2 + 1) n = codeBound n := by
    intro n
    induction n with
    | zero => simp [codeBound]
    | succ n ih =>
      simp only [unpair_pair_snd] at ih ⊢
      simp [codeBound, ih]
  exact (Nat.Primrec.prec1 1 hstep).of_eq haux

end Domain.Recursive
