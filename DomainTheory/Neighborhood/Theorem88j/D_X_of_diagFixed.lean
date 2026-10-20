/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88i
import DomainTheory.Neighborhood.Theorem88j.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)


variable {P qChar cons}

/-- **The reusable core of the surjectivity argument.** Any `V`-neighbourhood `P.X m` already
known to be `DiagFixed` (regardless of whether `m` itself is `myFoldCode`'s output) is `D_X qChar
cons c` for some list-code `c`: the singleton-list code witnessing `m` together with Part 1's
`qChar`-witness for it. -/
theorem D_X_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {m : ℕ} (hm : DiagFixed P a m) : ∃ c, D_X P qChar cons c = P.X m := by
  obtain ⟨i, hi⟩ := (hqChar m).mp hm
  refine ⟨encodeList [Nat.pair i m], ?_⟩
  have hstep : myFoldCode P qChar cons (encodeList [Nat.pair i m])
      = myStep P qChar cons P.masterIdx (Nat.pair i m) := by
    rw [myFoldCode_eq, decodeList_encodeList]
    unfold myFold
    rw [List.foldl_cons, List.foldl_nil]
  have hcond : cons (Nat.pair P.masterIdx m) = 1 := by
    apply (hcons P.masterIdx m).mpr
    refine ⟨m, ?_⟩
    have hsub : P.X m ⊆ V.master := V.sub_master (P.mem_X m)
    rw [P.masterIdx_spec]
    exact Set.subset_inter hsub subset_rfl
  have hstepval : myStep P qChar cons P.masterIdx (Nat.pair i m)
      = P.inter P.masterIdx m := by
    unfold myStep
    simp only [unpair_pair_snd]
    rw [(isOne_eq_one_iff _).mpr hi, (isOne_eq_one_iff _).mpr hcond, Nat.one_mul, selectFn_one]
  show D_X P qChar cons (encodeList [Nat.pair i m]) = P.X m
  unfold D_X
  rw [hstep, hstepval]
  have hcons' : (∃ k, P.X k ⊆ P.X P.masterIdx ∩ P.X m) := (hcons P.masterIdx m).mp hcond
  rw [P.inter_spec hcons', P.masterIdx_spec, Set.inter_eq_right.mpr (V.sub_master (P.mem_X m))]

end DomainTheory.Neighborhood
