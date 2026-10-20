module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- A monotone double `iSup` over `ℕ × ℕ` equals the diagonal `iSup`. -/
theorem iSup₂_monotone_eq_diagonal {α : Type*} [CompleteLattice α] (f : ℕ → ℕ → α)
    (hfm : ∀ n, Monotone (f n)) (hfn : ∀ m, Monotone (fun n => f n m)) :
    ⨆ n, ⨆ m, f n m = ⨆ n, f n n := by
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun m => ?_
    have hk : n ≤ n ⊔ m := le_sup_left
    have hk' : m ≤ n ⊔ m := le_sup_right
    calc f n m ≤ f (n ⊔ m) m := hfn m hk
      _ ≤ f (n ⊔ m) (n ⊔ m) := hfm (n ⊔ m) hk'
      _ ≤ ⨆ n', f n' n' := le_iSup (fun n' => f n' n') (n ⊔ m)
  · refine iSup_le fun n => le_trans (le_iSup (f n) n) (le_iSup (fun n' => ⨆ m, f n' m) n)

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
