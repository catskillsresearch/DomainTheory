/-ai
The projection tower in the recursion immediately before Theorem 4.4 is anchored at a continuous-lattice projection j_0 from [D_0 → D_0] onto D_0, and the successor of level n is the function-space projection induced by the projection at level n. At each successor the maps and the projection laws are the diagonal specialization of Proposition 3.7.
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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceProjection

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- The projection tower from Scott's recursion immediately before Theorem 4.4:
`j_{n+1} = [j_n → j_n]`, anchored at `j₀ : [D₀ → D₀] → D₀`.

At each successor, the maps and projection laws are the diagonal specialization
`proposition_3_7_projection P P`.  `conjMap` supplies the outer Scott-continuity needed to bundle
those canonical maps as an `IsContinuousLatticeProjection`. -/
noncomputable def towerProj (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) :
    ∀ n, IsContinuousLatticeProjection (towerType D₀ n) (towerType D₀ (n + 1))
  | 0 => j₀
  | (n + 1) => functionSpaceProjection (towerProj D₀ j₀ n)

end DomainTheory.ContinuousLattice
