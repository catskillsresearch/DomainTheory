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
import DomainTheory.Neighborhood.Recursive.RecDecidableu2eof_zero_one_char


namespace Domain.Recursive











































/-- **Paired `{0,1}` characteristic.** When the Bool decider has been packaged as a unary
primitive-recursive function on `Nat.pair n m`, reindex to `RecDecidable₂`. -/
theorem RecDecidable₂.of_paired_zero_one_char {r : ℕ → ℕ → Prop} {f : ℕ → ℕ} (hf : Nat.Primrec f)
    (h01 : ∀ t, f t = 0 ∨ f t = 1) (hfe : ∀ n m, r n m ↔ f (Nat.pair n m) = 1) :
    RecDecidable₂ r := by
  unfold RecDecidable₂
  refine RecDecidable.of_zero_one_char hf h01 (fun t => ?_)
  rw [hfe, pair_unpair]

end Domain.Recursive
