/-ai
The right projection is monotone with respect to inclusion of finite sets of sum tokens.

An element of the smaller projection is a right token of the smaller set, hence of the larger set by the inclusion, and therefore an element of the larger projection.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_rhtFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem rhtFinset_mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    rhtFinset v ⊆ rhtFinset u := by
  intro y hy
  exact (mem_rhtFinset).2 (h ((mem_rhtFinset).1 hy))

end InfoSys

end DomainTheory.InformationSystems
