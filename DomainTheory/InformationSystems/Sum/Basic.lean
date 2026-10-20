/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Proposition23

public import DomainTheory.InformationSystems.Sum.SumToken
public import DomainTheory.InformationSystems.Sum.sumBot
public import DomainTheory.InformationSystems.Sum.lftInsert
public import DomainTheory.InformationSystems.Sum.rhtInsert
public import DomainTheory.InformationSystems.Sum.lftFinset
public import DomainTheory.InformationSystems.Sum.rhtFinset
public import DomainTheory.InformationSystems.Sum.SumCon
public import DomainTheory.InformationSystems.Sum.SumEnt
public import DomainTheory.InformationSystems.Sum.sumSystem
public import DomainTheory.InformationSystems.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.Sum.mem_foldr_lft
public import DomainTheory.InformationSystems.Sum.mem_foldr_rht
public import DomainTheory.InformationSystems.Sum.mem_lftFinset
public import DomainTheory.InformationSystems.Sum.mem_rhtFinset
public import DomainTheory.InformationSystems.Sum.lftFinset_mono
public import DomainTheory.InformationSystems.Sum.rhtFinset_mono
public import DomainTheory.InformationSystems.Sum.lftFinset_insert_left
public import DomainTheory.InformationSystems.Sum.lftFinset_insert_right
public import DomainTheory.InformationSystems.Sum.lftFinset_insert_bot
public import DomainTheory.InformationSystems.Sum.rhtFinset_insert_right
public import DomainTheory.InformationSystems.Sum.rhtFinset_insert_left
public import DomainTheory.InformationSystems.Sum.rhtFinset_insert_bot
public import DomainTheory.InformationSystems.Sum.lftFinset_singleton_left
public import DomainTheory.InformationSystems.Sum.rhtFinset_singleton_right
public import DomainTheory.InformationSystems.Sum.lftFinset_singleton_bot
public import DomainTheory.InformationSystems.Sum.rhtFinset_singleton_bot
public import DomainTheory.InformationSystems.Sum.SumCon_rht_empty_of_lft_nonempty
public import DomainTheory.InformationSystems.Sum.SumCon_lft_empty_of_rht_nonempty
public import DomainTheory.InformationSystems.Sum.SumCon_lft_con_of_lft_nonempty
public import DomainTheory.InformationSystems.Sum.SumCon_rht_con_of_rht_nonempty

@[expose] public section

/-!
# Separated sum of information systems — Definition 6.3

**Scott 1982, Definition 6.3.** Tokens of `A + B` are left copies `(X, Δ)`, right
copies `(Δ, Y)`, and a fresh bottom `(Δ, Δ)`. Consistency and entailment are
disjunctive: a consistent set lives entirely on the left or entirely on the right
(or is empty / `{⊥}`).

We encode tokens as an inductive type so that `(Δ_A, Δ)`, `(Δ, Δ_B)`, and `(Δ, Δ)`
remain pairwise distinct, matching Scott’s remark after Def 6.3.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)






























end InfoSys
end DomainTheory.InformationSystems
