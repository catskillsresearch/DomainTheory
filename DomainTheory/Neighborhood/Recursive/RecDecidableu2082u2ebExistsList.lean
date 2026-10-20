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
import DomainTheory.Neighborhood.Recursive.existsListChar_eq_one_iff
import DomainTheory.Neighborhood.Recursive.primrec_existsListChar


namespace Domain.Recursive





















































































































































/-- **Bounded `∃` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∃ e ∈ decodeList c, q e p` is too. Choice-free. -/
theorem RecDecidable₂.bExistsList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∃ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => existsListChar g t.unpair.2 t.unpair.1, primrec_existsListChar hgp, fun t => ?_⟩
  show (∃ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ existsListChar g t.unpair.2 t.unpair.1 = 1
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this

end Domain.Recursive
