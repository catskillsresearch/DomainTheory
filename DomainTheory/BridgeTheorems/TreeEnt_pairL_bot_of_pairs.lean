/-ai
If a consistent finite set of tree tokens has a nonempty pair-left projection or a nonempty pair-right projection, then the set entails pair-left of bottom.

The atom set is empty and both pair projections are consistent. The entailment payload is the pair-left disjunct when the pair-left projection is nonempty, and the pair-right disjunct, with the entailed component equal to bottom, when the pair-right projection is nonempty.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem TreeEnt_pairL_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairL .bot) :=
  ⟨hu, TreeCon_atoms_empty_of_right A hu h,
    TreeCon_pairL_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    TreeCon_pairR_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inl ⟨hL, trivial⟩) (fun hR => Or.inr ⟨rfl, hR⟩)⟩

end DomainTheory.BridgeTheorems
