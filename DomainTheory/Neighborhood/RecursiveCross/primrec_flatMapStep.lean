/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RecursiveCross.Basic
import DomainTheory.Neighborhood.RecursiveCross.primrec_appendCode


namespace Domain.Recursive




















theorem primrec_flatMapStep {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (flatMapStep f) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (primrec_appendCode.comp ((hf.comp (hx.pair hy)).pair hacc)).of_eq fun w => by
    unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
