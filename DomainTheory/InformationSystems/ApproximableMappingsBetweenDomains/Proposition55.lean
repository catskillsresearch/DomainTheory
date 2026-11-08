module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55.comp

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem proposition_5_5 :
    ∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
      (g : ApproximableMap B C) (f : ApproximableMap A B) (x : A.Element),
      (comp g f).toElement x = g.toElement (f.toElement x) :=
  @comp.toElement

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
