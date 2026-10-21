/-ai
A finite set of sum tokens is sum-consistent, in the sense of Scott's Definition 6.3(iii), when its left projection is consistent in A and its right projection is empty, or its left projection is empty and its right projection is consistent in B.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Consistency for the separated sum (Scott 6.3(iii)). -/
def SumCon (u : Finset (SumToken α β)) : Prop :=
  (lftFinset u ∈ A.Con ∧ rhtFinset u = ∅) ∨
    (lftFinset u = ∅ ∧ rhtFinset u ∈ B.Con)

end InfoSys

end DomainTheory.InformationSystems
