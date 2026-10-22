module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_rht

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

omit [DecidableEq α] in

theorem mem_rhtFinset {u : Finset (SumToken α β)} {y : β} :
    y ∈ rhtFinset u ↔ SumToken.right y ∈ u := by
  unfold rhtFinset
  rw [mem_foldr_rht]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hy
    exact ⟨.right y, hy, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
