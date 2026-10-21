/-ai
Evaluating the constant map at an element b on the least element of the unit returns b.

This is the evaluation identity for constant maps, applied at the least element of the unit.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- Elements of `|A|` are in bijection with approximable maps `1 → A` via `const`. -/
theorem toElement_constMap_bot (b : A.Element) :
    (constMap (A := unitSystem) b).toElement unitSystem.botElement = b :=
  constMap_toElement b unitSystem.botElement

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
