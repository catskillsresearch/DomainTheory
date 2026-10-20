module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.sumBot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumEnt
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.sumSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_lft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_rht
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_mono
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_mono
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_insert_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_insert_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_insert_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_insert_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_insert_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_insert_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_singleton_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_singleton_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_singleton_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_singleton_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_rht_empty_of_lft_nonempty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_lft_empty_of_rht_nonempty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_lft_con_of_lft_nonempty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_rht_con_of_rht_nonempty

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
