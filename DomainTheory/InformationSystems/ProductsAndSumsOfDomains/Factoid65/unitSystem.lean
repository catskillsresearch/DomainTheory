/-ai
The unit information system has the unique token of the unit type as its least token, takes every finite set to be consistent, and takes entailment to hold of every finite set and every token. Each of the six information-system axioms holds because its conclusion is immediate.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- **Factoid 6.5.** The unit information system on a singleton token type. -/
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
