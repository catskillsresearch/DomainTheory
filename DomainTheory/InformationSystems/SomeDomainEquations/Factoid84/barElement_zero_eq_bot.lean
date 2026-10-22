module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_botElement

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84


theorem barElement_zero_eq_bot : barElement 0 = botElement := by
  apply le_antisymm
  · intro x hx
    rcases (mem_barElement 0 x).1 hx with rfl | rfl
    · exact (mem_botElement 0).2 rfl
    · exact (mem_botElement 0).2 rfl
  · intro x hx
    have : x = 0 := (mem_botElement x).1 hx
    subst this
    exact (mem_barElement 0 0).2 (Or.inl rfl)

end Factoid84
end DomainTheory.InformationSystems
