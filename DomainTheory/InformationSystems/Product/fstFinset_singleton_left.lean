/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.Product.BasicInst5
public import DomainTheory.InformationSystems.Product.ProdToken
public import DomainTheory.InformationSystems.Product.BasicInst7
public import DomainTheory.InformationSystems.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.Product.fstFinset
public import DomainTheory.InformationSystems.Product.fstFinset_empty
public import DomainTheory.InformationSystems.Product.fstFinset_insert_left

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem fstFinset_singleton_left (p : ProdToken A B) (hp : p.val.2 = B.bot) :
    fstFinset A B {p} = {p.val.1} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, fstFinset_insert_left A B ∅ p hp,
    fstFinset_empty]
  rfl

end InfoSys

end DomainTheory.InformationSystems
