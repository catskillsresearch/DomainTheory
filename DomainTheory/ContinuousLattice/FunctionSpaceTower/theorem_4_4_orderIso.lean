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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_projInfInf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- Lattice isomorphism along the same pair `i_∞`, `j_∞`. Scott's abstract also says the spaces
are isomorphic; this is not the statement of Theorem 4.4 (that statement is the homeomorphism). -/
noncomputable def theorem_4_4_orderIso : OrderIso (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  (Equiv.mk (embInfInf D₀ j₀) (projInfInf D₀ j₀)
      (projInfInf_embInfInf D₀ j₀) (embInfInf_projInfInf D₀ j₀)).toOrderIso
    (embInfInf D₀ j₀).monotone (projInfInf D₀ j₀).monotone

end Thm44d

end LimitMaps

end DomainTheory.ContinuousLattice
