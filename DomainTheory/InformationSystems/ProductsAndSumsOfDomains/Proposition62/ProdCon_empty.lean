/-ai
The empty set of product tokens is product-consistent.

Both projections of the empty set are empty, and the empty set is consistent in each factor.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

theorem ProdCon_empty : ProdCon A B (∅ : Finset (ProdToken A B)) :=
  ⟨by rw [fstFinset_empty]; exact A.con_empty,
    by rw [sndFinset_empty]; exact B.con_empty⟩

end InfoSys

end DomainTheory.InformationSystems
