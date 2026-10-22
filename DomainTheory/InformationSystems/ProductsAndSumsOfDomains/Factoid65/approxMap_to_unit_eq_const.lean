module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.unitElement_eq_bot

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap_unique
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- There is a unique approximable map into `1`, namely `const(⊥_1)`. -/
theorem approxMap_to_unit_eq_const (f : ApproximableMap A unitSystem) :
    f = constMap (A := A) unitSystem.botElement :=
  constMap_unique unitSystem.botElement f fun x => unitElement_eq_bot (f.toElement x)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
