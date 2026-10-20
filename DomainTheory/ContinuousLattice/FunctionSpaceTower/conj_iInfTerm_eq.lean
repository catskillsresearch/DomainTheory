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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm
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

/-- **Diagonal simplification.** `conjMap (j_{∞n}, i_{n∞})` applied to the `n`-th summand of `i_∞`
recovers the component `x_{n+1}`. This is Proposition 3.7's equation
`j_{[·]} ∘ i_{[·]} = id`, diagonally specialized to the projection from Proposition 4.2. -/
theorem conj_iInfTerm_eq (n : ℕ) (x : DInf D₀ j₀) :
    conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
            (embInf (towerType D₀) (towerProj D₀ j₀) n)
            (iInfTerm D₀ j₀ n x) = x.1 (n + 1) :=
  (proposition_3_7_projection
      (proposition_4_2 (towerType D₀) (towerProj D₀ j₀) n)
      (proposition_4_2 (towerType D₀) (towerProj D₀ j₀) n)).retr_incl
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) x)

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
