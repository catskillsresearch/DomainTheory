/-ai
The closure of a consistent finite set is the element whose carrier consists of the tokens entailed by that set. A finite set of such tokens is consistent because the original set entails it, so Proposition 2.3 makes the union consistent and the finite set is a subset of the union. The carrier is deductively closed because any finite set drawn from it is consistent by the same proposition, and entailment through that finite set is transitive.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23

public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.5.** Entailment closure of a consistent set. -/
def closure (u : Finset α) (hu : u ∈ sys.Con) : sys.Element where
  carrier := {X | sys.Ent u X}
  consistent := by
    intro Y hY
    have hEnt : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
    exact sys.con_subset (proposition_2_3_ii sys hu hEnt) (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3_ii sys hu hEntY) (subset_funion_right _ _)
    exact sys.ent_trans hu hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

end InfoSys

end DomainTheory.InformationSystems
