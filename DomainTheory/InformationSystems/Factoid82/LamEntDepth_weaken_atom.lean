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
public import DomainTheory.InformationSystems.Factoid82.lamAtomFinset_mono
public import DomainTheory.InformationSystems.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.Factoid82.LamConDepth_of_fun_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Weaken atom-entailment when the larger set stays in the atom world (`fun = ∅`). -/
theorem LamEntDepth_weaken_atom {u v : Finset (RawLamToken α)} {x : α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hFv : lamFunFinset v = ∅)
    (ht : LamEntDepth A u (.atom x)) : LamEntDepth A v (.atom x) := by
  cases ht with
  | atom hu hF hne hEnt =>
    have hsubA := lamAtomFinset_mono huv
    have hne' : lamAtomFinset v ≠ ∅ := by
      intro hAv
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact Finset.notMem_empty y (by have := hsubA hy; rwa [hAv] at this)
    exact LamEntDepth.atom hv hFv hne'
      (A.ent_trans ((LamConDepth_of_fun_empty A hFv).1 hv)
        ((LamConDepth_of_fun_empty A hF).1 hu)
        (fun y hy => A.ent_refl ((LamConDepth_of_fun_empty A hFv).1 hv) (hsubA hy))
        hEnt)

end InfoSys

end DomainTheory.InformationSystems
