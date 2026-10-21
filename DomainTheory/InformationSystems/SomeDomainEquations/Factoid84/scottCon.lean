/-ai
Scott's consistency remark says that, for an approximable map r on the powerset system P, a finite set u of tokens is consistent when the finite element of 1 is not contained in the image under r of the entailment closure of u.
ai-/
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
