/-ai
If a finite set w is consistent in B, then the right sum lift of w is consistent in the separated sum of A and B.

The left projection of the lift is empty, and the right projection of the lift equals w, so the right disjunct of sum consistency applies.
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

theorem SumCon_liftSumRight {w : Finset β} (hw : w ∈ B.Con) :
    SumCon A B (liftSumRight (α := α) w) :=
  Or.inr ⟨lftFinset_liftSumRight (α := α) w, by rw [rhtFinset_liftSumRight]; exact hw⟩

end InfoSys
end DomainTheory.InformationSystems
