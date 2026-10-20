module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.fstFinset_liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.sndFinset_liftLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem ProdCon_liftLeft {v : Finset α} (hv : v ∈ A.Con) :
    ProdCon A B (liftLeft A B v) := by
  refine ⟨?_, ?_⟩
  · rw [fstFinset_liftLeft]
    exact hv
  · exact B.con_subset (B.con_sing B.bot) (sndFinset_liftLeft A B v)

end InfoSys
end DomainTheory.InformationSystems
