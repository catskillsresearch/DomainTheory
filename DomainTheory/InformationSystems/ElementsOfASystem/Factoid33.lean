module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33.botElement

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_33 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element),
      sys.botElement ≤ x :=
  @botElement.le

end DomainTheory.InformationSystems.InfoSys
