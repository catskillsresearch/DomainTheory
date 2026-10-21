/-ai
The bottom element equals the entailment closure of the empty set.

Both inclusions are transitivity of entailment. A token entailed by the singleton of the bottom token is entailed by the empty set, because the empty set entails the bottom token. A token entailed by the empty set is entailed by the singleton of the bottom token, because no token lies in the empty set.
ai-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- `⊥ = ∅̄`. -/
theorem botElement_eq_closure_empty :
    sys.botElement = sys.closure (∅ : Finset α) sys.con_empty := by
  refine le_antisymm ?_ ?_
  · intro a ha
    -- ha : Ent {bot} a; show Ent ∅ a
    exact sys.ent_trans sys.con_empty (sys.con_sing sys.bot)
      (fun y hy => by
        have : y = sys.bot := Finset.mem_singleton.mp hy
        subst this
        exact sys.ent_bot sys.con_empty)
      ha
  · intro a ha
    -- ha : Ent ∅ a; show Ent {bot} a
    exact sys.ent_trans (sys.con_sing sys.bot) sys.con_empty
      (fun _ hy => False.elim (Finset.notMem_empty _ hy)) ha

end InfoSys
end DomainTheory.InformationSystems
