module

public import DomainTheory.InformationSystems.ElementsOfASystem.botElement

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem factoid_3_3 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element),
      sys.botElement ≤ x :=
  @botElement.le

end DomainTheory.InformationSystems.InfoSys
