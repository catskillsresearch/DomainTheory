module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.unitSystem

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- Elements of `|A|` are in bijection with approximable maps `1 → A` via `const`. -/
theorem toElement_constMap_bot (b : A.Element) :
    (constMap (A := unitSystem) b).toElement unitSystem.botElement = b :=
  constMap.toElement b unitSystem.botElement

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
