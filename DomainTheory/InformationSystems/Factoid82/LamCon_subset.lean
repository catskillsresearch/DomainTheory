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



theorem LamCon_subset {u : Finset (RawLamToken α)} (hu : LamCon A u) :
    ∀ {v}, v ⊆ u → LamCon A v := by
  rcases hu with ⟨n, hu⟩
  induction n generalizing u with
  | zero =>
    intro v hv
    refine ⟨0, ?_⟩
    change lamAtomFinset v ∈ A.Con ∧ lamFunFinset v = ∅
    rcases (hu : lamAtomFinset u ∈ A.Con ∧ lamFunFinset u = ∅) with ⟨hA, hF⟩
    exact ⟨A.con_subset hA (lamAtomFinset_mono hv),
      Finset.Subset.antisymm
        (fun p hp => by
          have : p ∈ lamFunFinset u := lamFunFinset_mono hv hp
          rw [hF] at this; exact False.elim (Finset.notMem_empty p this))
        (Finset.empty_subset _)⟩
  | succ n ih =>
    intro v hv
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · exact ih hu hv
    · refine ⟨n + 1, Or.inr ⟨?_, ?_, ?_⟩⟩
      · exact Finset.Subset.antisymm
          (fun x hx => by
            have : x ∈ lamAtomFinset u := lamAtomFinset_mono hv hx
            rw [hA] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      · intro p hp; exact hWF p (lamFunFinset_mono hv hp)
      · intro s hs hIn
        exact hFun s (fun p hp => lamFunFinset_mono hv (hs hp)) hIn

end InfoSys
end DomainTheory.InformationSystems
