/-ai
For an approximable map on the powerset system P, Scott consistency of the empty set of tokens is equivalent to Scott's consistency condition on that map.

Simplifying the two definitions and replacing the finite element of 0 by the bottom element leaves definitionally identical statements.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement_zero_eq_bot

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84




















theorem scottCon_empty_iff_consistent (r : ApproximableMap P P) :
    scottCon r ∅ ↔ ConsistentApprox r := by
  simp only [scottCon, ConsistentApprox, barElement_zero_eq_bot]
  rfl

end Factoid84
end DomainTheory.InformationSystems
