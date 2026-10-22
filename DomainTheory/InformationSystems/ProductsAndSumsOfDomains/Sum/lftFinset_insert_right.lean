module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_lftFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem lftFinset_insert_right (u : Finset (SumToken α β)) (y : β) :
    lftFinset (insert (.right y) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert (.right y) u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

end InfoSys

end DomainTheory.InformationSystems
