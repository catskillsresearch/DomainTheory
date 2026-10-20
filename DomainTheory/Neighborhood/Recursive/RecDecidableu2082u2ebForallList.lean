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
import DomainTheory.Neighborhood.Recursive.primrec_allListChar


namespace Domain.Recursive





















































































































































/-- **Bounded `∀` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∀ e ∈ decodeList c, q e p` is too (the list is coded by
the first argument, `p` is a free parameter). Choice-free. -/
theorem RecDecidable₂.bForallList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∀ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => allListChar g t.unpair.2 t.unpair.1, primrec_allListChar hgp, fun t => ?_⟩
  show (∀ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ allListChar g t.unpair.2 t.unpair.1 = 1
  rw [allListChar_eq_one_iff]
  refine forall_congr' fun e => forall_congr' fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this

end Domain.Recursive
