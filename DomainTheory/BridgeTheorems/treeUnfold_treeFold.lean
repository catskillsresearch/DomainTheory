module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeUnfold

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
