module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


/-- The unique element of `|1|` is `⊥`. -/
theorem unitElement_eq_bot (x : unitSystem.Element) : x = unitSystem.botElement := by
  apply le_antisymm
  · intro a ha
    cases a
    exact trivial
  · exact botElement_le unitSystem x

end InfoSys
end DomainTheory.InformationSystems
