module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.idMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem proposition_5_4 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (x : A.Element),
      (idMap A).toElement x = x :=
  @idMap.toElement

end DomainTheory.InformationSystems.InfoSys
