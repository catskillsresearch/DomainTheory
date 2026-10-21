/-ai
The right projection of the singleton consisting of the right token of an element is the singleton of that element.

After the membership characterization, membership in the projection is equality of right tokens. The right constructor is injective, and an equality of elements substitutes to an equality of right tokens.
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

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

omit [DecidableEq α] in

theorem rhtFinset_singleton_right (y : β) :
    rhtFinset ({.right y} : Finset (SumToken α β)) = {y} := by
  ext z
  simp only [mem_rhtFinset, Finset.mem_singleton]
  exact ⟨SumToken.right.inj, fun h => h ▸ rfl⟩

end InfoSys

end DomainTheory.InformationSystems
