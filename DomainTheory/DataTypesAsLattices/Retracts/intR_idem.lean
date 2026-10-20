/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intR_bot
public import DomainTheory.DataTypesAsLattices.Retracts.intR_ofNat
public import DomainTheory.DataTypesAsLattices.Retracts.intR_top_of_nonsingleton
public import DomainTheory.DataTypesAsLattices.Retracts.intR_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem intR_idem (x : Pomega) : funOf intR (funOf intR x) = funOf intR x := by
  by_cases hbot : x = botElem
  · subst hbot
    rw [intR_bot, intR_bot]
  · by_cases hsing : ∃ n, x = ofNat n
    · obtain ⟨n, rfl⟩ := hsing
      rw [intR_ofNat, intR_ofNat]
    · have hx : funOf intR x = topElem := by
        have hne : x.Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          simpa [botElem] using hbot
        exact intR_top_of_nonsingleton (sInf x) x (Nat.sInf_mem hne)
          (fun k hk => Nat.sInf_le hk) hbot (fun n hn => hsing ⟨n, hn⟩)
      rw [hx, intR_top]

end DomainTheory.DataTypesAsLattices
