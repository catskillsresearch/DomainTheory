/-ai
A product token lies in the left lift of a finite set v if and only if it is the left tag of some member of v.

Unfold the left lift and apply the membership characterization of the corresponding fold.
ai-/
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


theorem mem_liftLeft {v : Finset α} {p : ProdToken A B} :
    p ∈ liftLeft A B v ↔ ∃ x ∈ v, p = mkLeft A B x := by
  unfold liftLeft
  exact mem_foldr_liftLeft A B v.1 p

end InfoSys
end DomainTheory.InformationSystems
