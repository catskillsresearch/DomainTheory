/-ai
This file gathers and re-exports the product of two information systems: the product-token predicate and its decision procedure, product tokens and decidable equality, the product least token, the left and right projections of a finite set of product tokens together with membership, emptiness, monotonicity, insertion, and singleton laws, the left-commutativity of those insertions, product consistency, product entailment, and the product system. Scott's Definition 6.1 takes as tokens the pairs whose first component is least or whose second component is least, takes the pair of the two least tokens as least, and lets consistency and entailment act through the two projections.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.IsProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.prodBot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdCon
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdEnt
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_foldr_fst
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_foldr_snd
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_fstFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_mono
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_mono
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_insert_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_insert_not_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_insert_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_insert_not_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset_singleton_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset_singleton_right

@[expose] public section

/-!
# Product of information systems — Definition 6.1

**Scott 1982, Definition 6.1.** Tokens of `A × B` are pairs of the form
`(X, Δ_B)` or `(Δ_A, Y)`, with `Δ = (Δ_A, Δ_B)`. Consistency and entailment act
independently on the two projections `fst u` and `snd u`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]





variable (A : InfoSys α) (B : InfoSys β)






















end InfoSys
end DomainTheory.InformationSystems
