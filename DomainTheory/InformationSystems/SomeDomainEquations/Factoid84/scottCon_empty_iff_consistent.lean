module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.DomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.scottCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatRel
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_topElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.BotApprox_any
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
