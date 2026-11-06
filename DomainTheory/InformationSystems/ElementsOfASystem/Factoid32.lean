module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32.factoid_3_2

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_32 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element),
      sys.bot ∈ x.carrier :=
  @factoid_3_2

end DomainTheory.InformationSystems.InfoSys
