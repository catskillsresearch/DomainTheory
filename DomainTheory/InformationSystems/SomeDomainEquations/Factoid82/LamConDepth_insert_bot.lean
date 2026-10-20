/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Inserting bot preserves depth-Con. -/
theorem LamConDepth_insert_bot {u : Finset (RawLamToken α)}
    (hu : LamConDepth A u) :
    LamConDepth A (insert (.bot : RawLamToken α) u) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  by_cases hF : lamFunFinset u = ∅
  · have hF' : lamFunFinset (insert (.bot : RawLamToken α) u) = ∅ := by
      rw [lamFunFinset_insert_bot]; exact hF
    exact (LamConDepth_of_fun_empty A hF').2 (by
      rw [lamAtomFinset_insert_bot]
      exact (LamConDepth_of_fun_empty A hF).1 hu)
  · have hu' := (LamConDepth_of_fun_nonempty A hF).1 hu
    rcases hu' with ⟨hA, hWF, hFun⟩
    have hF' : lamFunFinset (insert (.bot : RawLamToken α) u) ≠ ∅ := by
      rw [lamFunFinset_insert_bot]; exact hF
    refine (LamConDepth_of_fun_nonempty A hF').2 ⟨?_, ?_, ?_⟩
    · rw [lamAtomFinset_insert_bot]; exact hA
    · intro p hp
      rw [lamFunFinset_insert_bot] at hp
      exact hWF p hp
    · intro s hs hIn
      refine hFun s (by rw [← lamFunFinset_insert_bot u]; exact hs) hIn

end InfoSys

end DomainTheory.InformationSystems
