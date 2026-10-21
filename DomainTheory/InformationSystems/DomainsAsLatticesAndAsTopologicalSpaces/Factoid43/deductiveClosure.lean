/-ai
The deductive closure of a finitely consistent set of tokens is the element whose tokens are those entailed by some finite subset of the set. A finite subset of this closure is entailed by some finite subset of the original set, and consistency of a set with the finite set it entails, followed by passage to a subset, makes that finite subset consistent. A further entailment is absorbed by transitivity of entailment along the same finite subset.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.IsFinitelyConsistent
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.exists_entSet_of_subset_deductive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Deductive closure of a finitely consistent set. -/
def deductiveClosure (U : Set α) (hU : sys.IsFinitelyConsistent U) : sys.Element where
  carrier := {a | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a}
  consistent := by
    intro Y hY
    obtain ⟨w, hwU, hEnt⟩ := sys.exists_entSet_of_subset_deductive U hU Y hY
    have hw : w ∈ sys.Con := hU w hwU
    exact sys.con_subset (proposition_2_3_ii sys hw hEnt) (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    obtain ⟨w, hwU, hEntY⟩ := sys.exists_entSet_of_subset_deductive U hU Y hY
    have hw : w ∈ sys.Con := hU w hwU
    have hYcon : Y ∈ sys.Con :=
      sys.con_subset (proposition_2_3_ii sys hw hEntY) (subset_funion_right _ _)
    exact ⟨w, hwU, sys.ent_trans hw hYcon hEntY hEnt⟩

end InfoSys

end DomainTheory.InformationSystems
