module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.toElement_constMap_bot

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem theorem_65 :
    ∀ {α : Type*} [DecidableEq α] {A : InfoSys α} (b : A.Element),
      (constMap (A := unitSystem) b).toElement unitSystem.botElement = b :=
  @toElement_constMap_bot

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
