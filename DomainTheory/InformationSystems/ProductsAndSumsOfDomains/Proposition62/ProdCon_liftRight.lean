module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.sndFinset_liftRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.fstFinset_liftRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem ProdCon_liftRight {w : Finset β} (hw : w ∈ B.Con) :
    ProdCon A B (liftRight A B w) := by
  refine ⟨?_, ?_⟩
  · exact A.con_subset (A.con_sing A.bot) (fstFinset_liftRight A B w)
  · rw [sndFinset_liftRight]
    exact hw

end InfoSys
end DomainTheory.InformationSystems
