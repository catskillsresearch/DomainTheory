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





















/-- Atom/bot-only sets that are consistent at stage `n` are consistent at stage `0`. -/
theorem LamConN_down_atom {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hF : lamFunFinset u = ∅) : LamConN A 0 u := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hF
    · exact ⟨by rw [hA]; exact A.con_empty, hF⟩

end InfoSys
end DomainTheory.InformationSystems
