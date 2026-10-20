/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomInsert

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u
variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)


instance : LeftCommutative (atomInsert : TreeToken α → Finset α → Finset α) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def atomFinset (u : Finset (TreeToken α)) : Finset α :=
  Multiset.foldr atomInsert (∅ : Finset α) u.1

end InfoSys
end DomainTheory.InformationSystems
