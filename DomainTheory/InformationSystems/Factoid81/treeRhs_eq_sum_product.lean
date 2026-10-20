/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Product
import DomainTheory.InformationSystems.Sum
import DomainTheory.InformationSystems.Factoid81.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u




variable {α : Type*} [DecidableEq α]















































variable (A : InfoSys α)


























theorem treeRhs_eq_sum_product :
    treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
