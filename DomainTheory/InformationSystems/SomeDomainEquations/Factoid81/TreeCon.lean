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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u
variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

/-- Consistency for trees (Scott §8 (4)–(7)). -/
inductive TreeCon : Finset (TreeToken α) → Prop where
  | left (u : Finset (TreeToken α))
      (hA : atomFinset u ∈ A.Con)
      (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅) : TreeCon u
  | right (u : Finset (TreeToken α))
      (hA : atomFinset u = ∅)
      (hL : TreeCon (pairLFinset u)) (hR : TreeCon (pairRFinset u)) : TreeCon u

end InfoSys
end DomainTheory.InformationSystems
