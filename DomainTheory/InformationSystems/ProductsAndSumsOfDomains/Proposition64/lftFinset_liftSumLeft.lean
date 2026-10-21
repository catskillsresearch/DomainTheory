/-ai
The left projection of the left sum lift of a finite set v of tokens of A equals v.

Extensionality, rewritten by the two membership characterizations, identifies a left token of the lift with the left constructor of some member of v, and injectivity of that constructor recovers the member. Conversely, each member of v is the component of its own left constructor in the lift.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumLeft

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

theorem lftFinset_liftSumLeft (v : Finset α) :
    lftFinset (liftSumLeft (β := β) v) = v := by
  ext x
  simp only [mem_lftFinset, mem_liftSumLeft]
  exact ⟨fun ⟨y, hy, h⟩ => by injection h with h'; exact h' ▸ hy,
    fun hx => ⟨x, hx, rfl⟩⟩

end InfoSys

end DomainTheory.InformationSystems
