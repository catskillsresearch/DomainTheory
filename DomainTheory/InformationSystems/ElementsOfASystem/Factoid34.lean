module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.exists_top_iff_allConsistent

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_34 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α),
      (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent :=
  @exists_top_iff_allConsistent

end DomainTheory.InformationSystems.InfoSys
