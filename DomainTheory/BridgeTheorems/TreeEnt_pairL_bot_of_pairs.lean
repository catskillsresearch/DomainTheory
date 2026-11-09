module

public import DomainTheory.InformationSystems.SomeDomainEquations.treeSystem

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem TreeEnt_pairL_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairL .bot) :=
  ⟨hu, TreeCon.atoms_empty_of_right A hu h,
    TreeCon.pairL_of_right A hu (TreeCon.atoms_empty_of_right A hu h),
    TreeCon.pairR_of_right A hu (TreeCon.atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inl ⟨hL, trivial⟩) (fun hR => Or.inr ⟨rfl, hR⟩)⟩

end DomainTheory.BridgeTheorems
