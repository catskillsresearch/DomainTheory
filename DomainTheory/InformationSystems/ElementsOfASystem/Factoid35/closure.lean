
module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23

public import DomainTheory.InformationSystems.InformationSystems.Proposition23
@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def closure (u : Finset α) (hu : u ∈ sys.Con) : sys.Element where
  carrier := {X | sys.Ent u X}
  consistent := by
    intro Y hY
    have hEnt : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
    exact sys.con_subset (proposition_2_3.ii sys hu hEnt) (funion.subset_right _ _)
  closed := by
    intro Y a hY hEnt
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3.ii sys hu hEntY) (funion.subset_right _ _)
    exact sys.ent_trans hu hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

end InfoSys

end DomainTheory.InformationSystems
