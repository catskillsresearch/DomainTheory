module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.PEnt

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- **Powerset information system.** Tokens `ℕ`, bot `0`, every finite set
consistent, minimal entailment. -/
def P : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := PEnt
  con_subset := fun _ _ => trivial
  con_sing := fun _ => trivial
  ent_con := fun _ => trivial
  ent_bot := fun _ => Or.inl rfl
  ent_refl := fun _ ha => Or.inr ha
  ent_trans := by
    intro u v c _ _ hEnts hc
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · exact hEnts c hc

end Factoid84

end DomainTheory.InformationSystems
