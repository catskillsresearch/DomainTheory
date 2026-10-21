/-ai
Every approximable map from the unit system into A equals the constant map at the element obtained by applying the map to the least element of the unit.

Uniqueness of constant maps applies once every element of the unit has been rewritten as the least element.
ai-/
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

/-- Every approximable map out of `1` is constant (Scott Factoid 6.5). -/
theorem approxMap_from_unit_eq_const (f : ApproximableMap unitSystem A) :
    f = constMap (A := unitSystem) (f.toElement unitSystem.botElement) :=
  constMap_unique (f.toElement unitSystem.botElement) f fun x => by
    rw [unitElement_eq_bot x]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
