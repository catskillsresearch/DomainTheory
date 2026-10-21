/-ai
The empty set of sum tokens is sum-consistent.

Its left projection is empty, hence consistent in A, and its right projection is empty, so the left disjunct of sum consistency applies.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



variable (A : InfoSys α) (B : InfoSys β)


























theorem SumCon_empty : SumCon A B (∅ : Finset (SumToken α β)) :=
  Or.inl ⟨by rw [lftFinset_empty]; exact A.con_empty, by rw [rhtFinset_empty]⟩

end InfoSys
end DomainTheory.InformationSystems
