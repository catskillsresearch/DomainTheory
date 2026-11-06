module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.idMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_54 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (x : A.Element),
      (idMap A).toElement x = x :=
  @idMap.toElement

end DomainTheory.InformationSystems.InfoSys
