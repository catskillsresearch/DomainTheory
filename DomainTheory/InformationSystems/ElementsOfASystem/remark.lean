module

public import DomainTheory.InformationSystems.ElementsOfASystem.topElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

theorem remark :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α),
      (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent :=
  @topElement.exists_top_iff_allConsistent

end InfoSys
end DomainTheory.InformationSystems
