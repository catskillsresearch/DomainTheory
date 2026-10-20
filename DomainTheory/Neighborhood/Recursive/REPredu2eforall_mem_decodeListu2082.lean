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
import DomainTheory.Neighborhood.Recursive.decodeList_mapPairCode
import DomainTheory.Neighborhood.Recursive.primrec_mapPairCode


namespace Domain.Recursive



























































































































/-- **Parameterised bounded `∀` over a coded list preserves recursive enumerability.** If `p` is an
r.e. binary relation then `fun t => ∀ e ∈ decodeList t.2, p t.1 e` is r.e.: re-code the list into the
pairs `⟨t.1, e⟩` (`mapPairCode`) and apply the unparameterised `forall_mem_decodeList`. -/
theorem REPred.forall_mem_decodeList₂ {p : ℕ → ℕ → Prop} (hp : REPred₂ p) :
    REPred (fun t => ∀ e ∈ decodeList t.unpair.2, p t.unpair.1 e) := by
  have hp' : REPred (fun s => p s.unpair.1 s.unpair.2) := hp
  have hbase : REPred (fun c => ∀ e' ∈ decodeList c, p e'.unpair.1 e'.unpair.2) :=
    hp'.forall_mem_decodeList
  refine REPred.of_iff (fun t => ?_) (hbase.comp primrec_mapPairCode)
  rw [decodeList_mapPairCode]
  simp only [List.mem_reverse, List.mem_map]
  constructor
  · rintro hall e' ⟨e, he, rfl⟩
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact hall e he
  · intro hall e he
    simpa only [unpair_pair_fst, unpair_pair_snd]
      using hall (Nat.pair t.unpair.1 e) ⟨e, he, rfl⟩

end Domain.Recursive
