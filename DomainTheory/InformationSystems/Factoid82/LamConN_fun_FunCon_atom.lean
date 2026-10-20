/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Sum
import Mathlib.Data.Finset.Card
import DomainTheory.InformationSystems.Factoid82.Basic
import DomainTheory.InformationSystems.Factoid82.LamConN_empty
import DomainTheory.InformationSystems.Factoid82.LamConN_exists_FunCon
import DomainTheory.InformationSystems.Factoid82.LamConN_FunCon_mono_atom


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















/-- Full FunCon at stage `n+1` (uses `exists_FunCon` + atom-input lift).
Nested function tokens in the input union remain for the general `ent_con` argument. -/
theorem LamConN_fun_FunCon_atom {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A (n + 1) u)
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hIn : LamConN A n (lamInputUnion s))
    (hF : lamFunFinset (lamInputUnion s) = ∅) :
    LamConN A n (lamOutputUnion s) := by
  if hempty : s = ∅ then
    subst hempty
    simpa [lamOutputUnion_empty] using LamConN_empty A n
  else
    have hne : lamFunFinset u ≠ ∅ := by
      obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hempty
      exact Finset.ne_empty_of_mem (hs hp)
    rcases LamConN_exists_FunCon A hu hne with ⟨k, hk, _, _, hFun⟩
    have hkn : k ≤ n := Nat.le_of_succ_le_succ hk
    exact LamConN_FunCon_mono_atom A hkn hFun hs hIn hF

end InfoSys
end DomainTheory.InformationSystems
