/-ai
The bottom element is the set of tokens entailed by the singleton of the bottom token. A finite set of such tokens is consistent because that singleton is consistent and entails the finite set, so Proposition 2.3 makes the union consistent and the finite set is a subset of the union. The set is deductively closed because any finite set drawn from it is consistent by the same proposition, and entailment from the singleton through that finite set is transitive.
ai-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.3.** The bottom element `⊥ = {X ∣ {Δ} ⊢ X}`. -/
def botElement : sys.Element where
  carrier := {X | sys.Ent {sys.bot} X}
  consistent := by
    intro Y hY
    have hbot : ({sys.bot} : Finset α) ∈ sys.Con := sys.con_sing sys.bot
    have hEnt : sys.EntSet {sys.bot} Y := fun X hX => hY (Finset.mem_coe.2 hX)
    have hunion : {sys.bot} ∪' Y ∈ sys.Con := proposition_2_3_ii sys hbot hEnt
    exact sys.con_subset hunion (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    have hbot : ({sys.bot} : Finset α) ∈ sys.Con := sys.con_sing sys.bot
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet {sys.bot} Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3_ii sys hbot hEntY) (subset_funion_right _ _)
    exact sys.ent_trans hbot hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

end InfoSys

end DomainTheory.InformationSystems
