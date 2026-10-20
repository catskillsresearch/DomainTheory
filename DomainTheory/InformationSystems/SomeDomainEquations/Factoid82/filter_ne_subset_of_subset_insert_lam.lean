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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem filter_ne_subset_of_subset_insert_lam
    {p : List (RawLamToken α) × List (RawLamToken α)}
    {t w : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (ht : t ⊆ insert p w) : t.filter (· ≠ p) ⊆ w := by
  intro q hq
  have ⟨hqt, hne⟩ := Finset.mem_filter.mp hq
  have : q ∈ insert p w := ht hqt
  rcases Finset.mem_insert.mp this with rfl | hqW
  · exact False.elim (hne rfl)
  · exact hqW

end InfoSys

end DomainTheory.InformationSystems
