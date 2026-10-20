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











































/-- An always-true predicate is recursively decidable (constant decider `1`). -/
theorem recDecidable_of_forall {p : ℕ → Prop} (h : ∀ n, p n) : RecDecidable p :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun n => ⟨fun _ => rfl, fun _ => h n⟩⟩

end Domain.Recursive
