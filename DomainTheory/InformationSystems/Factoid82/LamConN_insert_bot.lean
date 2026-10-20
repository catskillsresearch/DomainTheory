/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



























theorem LamConN_insert_bot {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) : LamConN A n (insert (.bot : RawLamToken α) u) := by
  induction n generalizing u with
  | zero =>
    exact ⟨by rw [lamAtomFinset_insert_bot]; exact hu.1,
      by rw [lamFunFinset_insert_bot]; exact hu.2⟩
  | succ n ih =>
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · exact Or.inl (ih hu)
    · exact Or.inr ⟨by rw [lamAtomFinset_insert_bot]; exact hA,
        fun p hp => hWF p (by rwa [lamFunFinset_insert_bot] at hp),
        fun s hs hIn =>
          hFun s (fun p hp => by rw [← lamFunFinset_insert_bot u]; exact hs hp) hIn⟩

end InfoSys
end DomainTheory.InformationSystems
