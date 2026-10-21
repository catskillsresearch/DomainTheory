/-ai
The summands of the embedding i_∞ increase with the index: for each x in D_∞ and each m, the m-th summand at x lies below the (m+1)-st summand at x.

The pointwise order reduces the comparison to values at an arbitrary z. The successor formula for the inverse-limit embedding rewrites the lower value one level up, and monotonicity of the embedding at that level reduces the claim to an inequality of arguments. Inverse-limit coherence replaces the (m+1)-st component of x by the retraction of the next component. The successor formula for the tower retraction then moves the level-m inclusion inside that component. The projection inequality drops the inclusion-retraction pair, and monotonicity of the next component, fed by the inequality between an embedded component and the next projection, completes the comparison.
ai-/
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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj_succ_retr_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.incl_projInf_le_projInf_succ

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- `i_∞` is monotone in its summand index. -/
theorem iInfTerm_le_succ (x : DInf D₀ j₀) (m : ℕ) :
    iInfTerm D₀ j₀ m x ≤ iInfTerm D₀ j₀ (m + 1) x := by
  rw [ScottMap.le_def]
  intro z
  rw [iInfTerm_apply, iInfTerm_apply,
    ← embInf_succ (towerType D₀) (towerProj D₀ j₀) m
      (x.1 (m + 1) (projInf (towerType D₀) (towerProj D₀ j₀) m z))]
  refine embInf_monotone (towerType D₀) (towerProj D₀ j₀) (m + 1) ?_
  have hab : (towerProj D₀ j₀ m).incl (projInf (towerType D₀) (towerProj D₀ j₀) m z)
      ≤ projInf (towerType D₀) (towerProj D₀ j₀) (m + 1) z :=
    incl_projInf_le_projInf_succ D₀ j₀ m z
  calc (towerProj D₀ j₀ m).incl
          (x.1 (m + 1) (projInf (towerType D₀) (towerProj D₀ j₀) m z))
      = (towerProj D₀ j₀ m).incl
          (((towerProj D₀ j₀ (m + 1)).retr (x.1 (m + 2)))
            (projInf (towerType D₀) (towerProj D₀ j₀) m z)) := by
        rw [show ((towerProj D₀ j₀ (m + 1)).retr (x.1 (m + 2))) = x.1 (m + 1) from x.2 (m + 1)]
    _ = (towerProj D₀ j₀ m).incl
          ((towerProj D₀ j₀ m).retr
            (x.1 (m + 2) ((towerProj D₀ j₀ m).incl
              (projInf (towerType D₀) (towerProj D₀ j₀) m z)))) := by
        rw [towerProj_succ_retr_apply]
    _ ≤ x.1 (m + 2) ((towerProj D₀ j₀ m).incl
          (projInf (towerType D₀) (towerProj D₀ j₀) m z)) :=
        (towerProj D₀ j₀ m).incl_retr_le _
    _ ≤ x.1 (m + 2) (projInf (towerType D₀) (towerProj D₀ j₀) (m + 1) z) :=
        ScottMap.monotone (x.1 (m + 2)) hab

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
