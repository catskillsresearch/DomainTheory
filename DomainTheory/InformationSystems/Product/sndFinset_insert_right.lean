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
public import DomainTheory.InformationSystems.Product.sndFinset
public import DomainTheory.InformationSystems.Product.mem_sndFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem sndFinset_insert_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 = A.bot) :
    sndFinset A B (insert p u) = insert p.val.2 (sndFinset A B u) := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hy'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_sndFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hy'.symm⟩
    · rcases (mem_sndFinset A B).1 hy' with ⟨q, hq, hbot, hyq⟩
      exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hyq⟩

end InfoSys

end DomainTheory.InformationSystems
