module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_lft

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

omit [DecidableEq β] in

theorem mem_lftFinset {u : Finset (SumToken α β)} {x : α} :
    x ∈ lftFinset u ↔ SumToken.left x ∈ u := by
  unfold lftFinset
  rw [mem_foldr_lft]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hx
    exact ⟨.left x, hx, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
