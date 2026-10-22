module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


omit [DecidableEq β] in


theorem lftFinset_empty : lftFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (Finset.notMem_empty _ ((mem_lftFinset).1 hx))
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

end InfoSys
end DomainTheory.InformationSystems
