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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















theorem LamConN_fun_empty {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamAtomFinset u ≠ ∅) : lamFunFinset u = ∅ := by
  induction n generalizing u with
  | zero => exact hu.2
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hne
    · exact False.elim (hne hA)

end InfoSys
end DomainTheory.InformationSystems
