/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.IsProdToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

instance (A : InfoSys α) (B : InfoSys β) (p : α × β) : Decidable (IsProdToken A B p) :=
  if h1 : p.1 = A.bot then isTrue (Or.inl h1)
  else if h2 : p.2 = B.bot then isTrue (Or.inr h2)
  else isFalse fun h => h.elim h1 h2

end InfoSys

end DomainTheory.InformationSystems
