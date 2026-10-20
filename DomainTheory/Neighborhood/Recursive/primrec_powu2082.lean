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
import DomainTheory.Neighborhood.Recursive.primrec_pow


namespace Domain.Recursive



















































































/-- `fun n => f n ^ g n` is primitive recursive. -/
theorem primrec_pow₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n ^ g n) :=
  (primrec_pow.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
