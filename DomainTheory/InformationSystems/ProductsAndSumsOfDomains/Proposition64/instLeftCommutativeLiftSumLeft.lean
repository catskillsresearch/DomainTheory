/-ai
Insertion of a left sum token into a finite set of sum tokens is left-commutative, because insertion of two such tokens commutes.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

instance instLeftCommutativeLiftSumLeft :
    LeftCommutative fun x : α =>
      (insert (SumToken.left (β := β) x) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

end InfoSys

end DomainTheory.InformationSystems
