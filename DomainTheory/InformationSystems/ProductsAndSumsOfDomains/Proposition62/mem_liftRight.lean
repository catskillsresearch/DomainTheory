module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

theorem mem_liftRight {w : Finset β} {p : ProdToken A B} :
    p ∈ liftRight A B w ↔ ∃ y ∈ w, p = mkRight A B y := by
  unfold liftRight
  exact mem_foldr_liftRight A B w.1 p

end InfoSys
end DomainTheory.InformationSystems
