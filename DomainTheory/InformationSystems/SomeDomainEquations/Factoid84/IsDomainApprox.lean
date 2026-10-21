/-ai
An approximable map from the powerset system P to itself satisfies Scott's conditions (1) through (5) when it is reflexive and idempotent, contains the finite element of 0 in the image of the bottom element, sends the finite element of 1 to the top element, and does not contain the finite element of 1 in the image of the finite element of 0.
ai-/
module


public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.PEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.bar
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.botElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.topElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.ReflApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IdemApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.BotApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.RogueApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.ConsistentApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P_AllConsistent

@[expose] public section

namespace DomainTheory.InformationSystems
namespace Factoid84

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap


/-- Scott (1)–(5): approximable maps that present entailment relations / domains. -/
structure IsDomainApprox (r : ApproximableMap P P) : Prop where
  refl : ReflApprox r
  idem : IdemApprox r
  bot : BotApprox r
  rogue : RogueApprox r
  consistent : ConsistentApprox r

end Factoid84
end DomainTheory.InformationSystems
