module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairL_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairR_of_right

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem TreeEnt_pairL_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairL .bot) :=
  ⟨hu, TreeCon.atoms_empty_of_right A hu h,
    TreeCon.pairL_of_right A hu (TreeCon.atoms_empty_of_right A hu h),
    TreeCon.pairR_of_right A hu (TreeCon.atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inl ⟨hL, trivial⟩) (fun hR => Or.inr ⟨rfl, hR⟩)⟩

end DomainTheory.BridgeTheorems
