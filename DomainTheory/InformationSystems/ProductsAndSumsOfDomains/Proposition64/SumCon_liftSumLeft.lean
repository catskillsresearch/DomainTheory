/-ai
If a finite set v is consistent in A, then the left sum lift of v is consistent in the separated sum of A and B.

The left projection of the lift equals v, and the right projection of the lift is empty, so the left disjunct of sum consistency applies.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false













theorem SumCon_liftSumLeft {v : Finset α} (hv : v ∈ A.Con) :
    SumCon A B (liftSumLeft (β := β) v) :=
  Or.inl ⟨by rw [lftFinset_liftSumLeft]; exact hv, rhtFinset_liftSumLeft (β := β) v⟩

end InfoSys
end DomainTheory.InformationSystems
