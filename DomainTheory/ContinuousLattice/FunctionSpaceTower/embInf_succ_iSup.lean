module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
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

/-- The inverse-limit embedding commutes with a supremum in `D_{n+1}` (monotone ⇒ directed). -/
theorem embInf_succ_iSup (n : ℕ) (f : ℕ → towerType D₀ (n + 1)) (hf : Monotone f) :
    embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) (⨆ m, f m) =
      ⨆ m, embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) (f m) := by
  have hdir : DirectedOn (· ≤ ·) (Set.range f) :=
    directedOn_range.2 fun a b => ⟨max a b, hf (le_max_left a b), hf (le_max_right a b)⟩
  have hne := Set.range_nonempty f
  rw [show (⨆ m, f m) = sSup (Set.range f) from sSup_range.symm,
    (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)).preservesDirectedSup_coe
      (Set.range f) hne hdir, ← Set.range_comp]
  rfl

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
