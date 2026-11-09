module

public import DomainTheory.InformationSystems.InformationSystems.EntSet
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element

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
    exact sys.con_subset (EntSet.union_mem sys hu hEnt) (funion.subset_right _ _)
  closed := by
    intro Y a hY hEnt
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (EntSet.union_mem sys hu hEntY) (funion.subset_right _ _)
    exact sys.ent_trans hu hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

namespace closure

theorem subset {u : Finset α} (hu : u ∈ sys.Con) :
    ↑u ⊆ (sys.closure u hu).carrier :=
  fun _ hX => sys.ent_refl hu (Finset.mem_coe.1 hX)

theorem mem_iff {u : Finset α} (hu : u ∈ sys.Con) {X : α} :
    X ∈ (sys.closure u hu).carrier ↔ sys.Ent u X := Iff.rfl

end closure

theorem theorem_35 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u : Finset α} (hu : u ∈ sys.Con),
      ↑u ⊆ (sys.closure u hu).carrier :=
  @closure.subset

end InfoSys

end DomainTheory.InformationSystems
