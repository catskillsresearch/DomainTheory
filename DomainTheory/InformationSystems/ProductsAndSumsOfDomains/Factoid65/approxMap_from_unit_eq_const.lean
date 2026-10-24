module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.unitSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.unitElement_eq_bot

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- Every approximable map out of `1` is constant (Scott Factoid 6.5). -/
theorem approxMap_from_unit_eq_const (f : ApproximableMap unitSystem A) :
    f = constMap (A := unitSystem) (f.toElement unitSystem.botElement) :=
  constMap.unique (f.toElement unitSystem.botElement) f fun x => by
    rw [unitElement_eq_bot x]

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
