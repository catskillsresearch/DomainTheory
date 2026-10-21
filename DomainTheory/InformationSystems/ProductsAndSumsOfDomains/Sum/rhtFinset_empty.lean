/-ai
The right projection of the empty set of sum tokens is empty.

A member of that projection would be a right token belonging to the empty set, which is impossible, and the empty set has no members.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



variable (A : InfoSys α) (B : InfoSys β)












theorem rhtFinset_empty : rhtFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (Finset.notMem_empty _ ((mem_rhtFinset).1 hy))
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

end InfoSys
end DomainTheory.InformationSystems
