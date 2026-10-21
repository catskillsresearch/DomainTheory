/-ai
The empty set of tokens is flat-related to itself.

The containment clause holds because the empty set has no members, and 1 does not belong to the empty set.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatRel

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatRel_empty : flatRel ∅ ∅ :=
  Or.inr ⟨fun _ hn => False.elim (Finset.notMem_empty _ hn), Finset.notMem_empty _⟩

end Factoid84

end DomainTheory.InformationSystems
