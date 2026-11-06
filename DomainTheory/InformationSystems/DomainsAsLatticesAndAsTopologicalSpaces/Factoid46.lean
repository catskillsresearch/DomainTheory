module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toElement_ofScottContinuous

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem theorem_46 :
    ∀ {α β : Type*} [DecidableEq α] [DecidableEq β] {A : InfoSys α} {B : InfoSys β}
      (g : ScottContinuous A B) (x : A.Element),
      (ofScottContinuous g).toElement x = g.toFun x :=
  @toElement_ofScottContinuous

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
