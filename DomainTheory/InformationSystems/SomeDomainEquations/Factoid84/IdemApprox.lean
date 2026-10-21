/-ai
Scott's idempotence condition on an approximable map r from the powerset system P to itself says that the composite of r with itself equals r.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- (2) `r ∘ r = r` (transitivity / idempotence). -/
def IdemApprox (r : ApproximableMap P P) : Prop :=
  ApproximableMap.comp r r = r

end Factoid84

end DomainTheory.InformationSystems
