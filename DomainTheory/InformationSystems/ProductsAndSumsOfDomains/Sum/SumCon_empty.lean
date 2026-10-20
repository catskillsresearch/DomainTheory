/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



variable (A : InfoSys α) (B : InfoSys β)


























theorem SumCon_empty : SumCon A B (∅ : Finset (SumToken α β)) :=
  Or.inl ⟨by rw [lftFinset_empty]; exact A.con_empty, by rw [rhtFinset_empty]⟩

end InfoSys
end DomainTheory.InformationSystems
