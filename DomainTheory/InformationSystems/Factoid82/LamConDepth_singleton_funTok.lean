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
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.Factoid82.lamOutputUnion_empty
public import DomainTheory.InformationSystems.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.Factoid82.lamAtomFinset_singleton_funTok
public import DomainTheory.InformationSystems.Factoid82.lamFunFinset_singleton_funTok
public import DomainTheory.InformationSystems.Factoid82.lamOutputUnion_singleton
public import DomainTheory.InformationSystems.Factoid82.LamConDepth_empty
public import DomainTheory.InformationSystems.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.Factoid82.BasicInst74

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Singleton funTok is Con when components are (Scott (7) on a singleton). -/
theorem LamConDepth_singleton_funTok (xs ys : List (RawLamToken α))
    (hxs : LamConDepth A (listToFinset xs)) (hys : LamConDepth A (listToFinset ys)) :
    LamConDepth A ({.funTok xs ys} : Finset (RawLamToken α)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.funTok xs ys} : Finset (RawLamToken α)) = {(xs, ys)} :=
    lamFunFinset_singleton_funTok xs ys
  have hA : lamAtomFinset ({.funTok xs ys} : Finset (RawLamToken α)) = ∅ :=
    lamAtomFinset_singleton_funTok xs ys
  have hne : lamFunFinset ({.funTok xs ys} : Finset (RawLamToken α)) ≠ ∅ := by
    rw [hF]; exact Finset.singleton_ne_empty _
  refine (LamConDepth_of_fun_nonempty A hne).2 ⟨hA, ?_, ?_⟩
  · intro p hp
    have : p = (xs, ys) := Finset.mem_singleton.mp (hF ▸ hp)
    subst this; exact ⟨hxs, hys⟩
  · intro s hs hIn
    rw [hF] at hs
    by_cases hmem : (xs, ys) ∈ s
    · have hsin : s = {(xs, ys)} := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (hs hp))
        · intro hp
          have : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst this; exact hmem
      subst hsin
      rw [lamOutputUnion_singleton]
      exact hys
    · have hempty : s = ∅ := by
        ext p
        constructor
        · intro hp
          exact False.elim (hmem (by
            have : p = (xs, ys) := Finset.mem_singleton.mp (hs hp)
            subst this; exact hp))
        · intro hp; exact False.elim (Finset.notMem_empty p hp)
      subst hempty
      rw [lamOutputUnion_empty]
      exact LamConDepth_empty A

end InfoSys

end DomainTheory.InformationSystems
