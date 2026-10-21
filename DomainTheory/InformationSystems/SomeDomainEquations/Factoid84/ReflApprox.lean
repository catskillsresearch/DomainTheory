/-ai
Scott's reflexivity condition on an approximable map r from the powerset system P to itself says that every relation of the identity map of P is a relation of r.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- (1) `I_P ⊆ r` (reflexivity of the induced entailment). -/
def ReflApprox (r : ApproximableMap P P) : Prop :=
  ∀ {u v : Finset ℕ}, (idMap P).rel u v → r.rel u v

end Factoid84

end DomainTheory.InformationSystems
