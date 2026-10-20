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

theorem rhtFinset_insert_bot (u : Finset (SumToken α β)) :
    rhtFinset (insert (.bot : SumToken α β) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert .bot u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

end InfoSys

end DomainTheory.InformationSystems
