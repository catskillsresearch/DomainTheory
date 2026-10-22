/-ai
Folding the unfold of a tree token either returns the token, or else the token is pair-right of bottom and the fold of its unfold is pair-left of bottom.

The bottom and atom cases are equalities. A pair-left token folds back to itself. A pair-right token folds back to itself unless its component is tree bottom, in which case the fold is pair-left of bottom; the other constructors are not tree bottom.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem treeFold_eq_or_pairBots (t : TreeToken α) :
    treeFold A (treeUnfold A t) = t ∨
      t = .pairR .bot ∧ treeFold A (treeUnfold A t) = .pairL .bot := by
  cases t with
  | bot => exact Or.inl rfl
  | atom x => exact Or.inl rfl
  | pairL t =>
    refine Or.inl ?_
    simp [treeFold, treeUnfold, treeBot]
  | pairR t =>
    simp only [treeFold, treeUnfold, treeBot]
    split_ifs with hb
    · cases t with
      | bot => exact Or.inr ⟨rfl, rfl⟩
      | atom _ | pairL _ | pairR _ => exact False.elim (nomatch hb)
    · exact Or.inl (ite_eq_right hb)

end DomainTheory.BridgeTheorems
