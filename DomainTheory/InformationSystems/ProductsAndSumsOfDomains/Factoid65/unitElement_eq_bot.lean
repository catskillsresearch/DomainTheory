/-ai
The only element of the unit system is its least element.

Antisymmetry of the element order gives the two inclusions. A token of an arbitrary element is the unique token of the unit type, after which membership in the least element is immediate. The reverse inclusion is the general fact that the least element lies below every element.
ai-/
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
