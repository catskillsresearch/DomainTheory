/-ai
Unfolding the fold of a sum token returns that sum token.

The bottom and left cases are equalities. For a right product token whose second component is tree bottom, the fold is pair-left of the first component and unfolding restores the pair. Otherwise the product law forces the first component to be tree bottom, the fold is pair-right of the second component, and unfolding restores the pair.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem treeUnfold_treeFold (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    treeUnfold A (treeFold A s) = s := by
  cases s with
  | bot => rfl
  | left x => rfl
  | right p =>
    dsimp [treeFold, treeUnfold]
    split_ifs with hb
    · apply congrArg SumToken.right
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hb.symm
    · have ha : p.val.1 = treeBot := by
        rcases p.property with h1 | h2
        · exact h1
        · exact False.elim (hb h2)
      apply congrArg SumToken.right
      apply Subtype.ext
      apply Prod.ext
      · exact ha.symm
      · rfl

end DomainTheory.BridgeTheorems
