module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

/-- Scott’s consistency remark: for such an `r`, a finite `u` is “consistent”
when `\bar 1 ⊈ r(\bar u)`. -/
def scottCon (r : ApproximableMap P P) (u : Finset ℕ) : Prop :=
  ¬ ((barElement 1).carrier ⊆
      (r.toElement (P.closure u (by trivial))).carrier)

end Factoid84

end DomainTheory.InformationSystems
