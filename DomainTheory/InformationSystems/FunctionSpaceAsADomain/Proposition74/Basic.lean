module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem closure_empty_eq_bot :
    A.closure (∅ : Finset α) A.con_empty = A.botElement := by
  apply le_antisymm
  · intro a ha
    exact A.ent_trans (A.con_sing A.bot) A.con_empty (A.entSet_empty _) ha
  · intro a ha
    exact A.ent_trans A.con_empty (A.con_sing A.bot)
      (fun x hx => by
        have : x = A.bot := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_bot A.con_empty)
      ha
end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
