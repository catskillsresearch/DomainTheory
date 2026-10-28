module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

def unitSystem : InfoSys PUnit where
  bot := ⟨⟩
  Con := Set.univ
  Ent := fun _ _ => True
  con_subset := by
    intro u v _ _
    exact trivial
  con_sing := by
    intro _
    exact trivial
  ent_con := by
    intro u a _
    exact trivial
  ent_bot := by
    intro u _
    exact trivial
  ent_refl := by
    intro u a _ _
    exact trivial
  ent_trans := by
    intro u v c _ _ _ _
    exact trivial

end InfoSys

end DomainTheory.InformationSystems
