module

public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.idMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem idMap_botElement : (idMap A).toElement A.botElement = A.botElement :=
  idMap.toElement A A.botElement

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
