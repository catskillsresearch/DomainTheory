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
public import DomainTheory.InformationSystems.Product.mem_foldr_fst

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_fstFinset {u : Finset (ProdToken A B)} {x : α} :
    x ∈ fstFinset A B u ↔ ∃ p ∈ u, p.val.2 = B.bot ∧ p.val.1 = x := by
  unfold fstFinset
  rw [mem_foldr_fst]
  constructor
  · rintro ⟨p, hp, hx⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hx⟩
  · rintro ⟨p, hp, hbot, hx⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hx⟩

end InfoSys

end DomainTheory.InformationSystems
