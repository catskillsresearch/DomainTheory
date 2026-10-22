module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- `i_{n∞}(yₙ) ⊑ y_{n+1}`: climbing one level and embedding stays below the next component. -/
theorem incl_projInf_le_projInf_succ (n : ℕ) (w : DInf D₀ j₀) :
    (towerProj D₀ j₀ n).incl (projInf (towerType D₀) (towerProj D₀ j₀) n w)
      ≤ projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) w := by
  have h := (towerProj D₀ j₀ n).incl_retr_le
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) w)
  rwa [show (towerProj D₀ j₀ n).retr (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) w)
      = projInf (towerType D₀) (towerProj D₀ j₀) n w from w.2 n] at h

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
