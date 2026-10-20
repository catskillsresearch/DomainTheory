module


public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
import all Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
import all Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- **Scott 1972, Proposition 3.7 (projection half).** Under the same hypotheses with
projections, the induced pair on function spaces is also a projection. -/
structure ScottMapProjection (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] extends
    ScottMapRetraction D₀ D₀' D₁ D₁' where
  incl_retr_le : ∀ f' x, (incl (retr f')) x ≤ f' x

namespace ScottMapProjection

def functionSpace (P₀ : IsContinuousLatticeProjection D₀ D₀') (P₁ : IsContinuousLatticeProjection D₁ D₁') :
    ScottMapProjection D₀ D₀' D₁ D₁' where
  toScottMapRetraction :=
    ScottMapRetraction.functionSpace P₀.toIsContinuousLatticeRetraction P₁.toIsContinuousLatticeRetraction
  incl_retr_le f' y := by
    dsimp only [ScottMapRetraction.functionSpace, ScottMap.comp, Function.comp_def]
    exact le_trans (P₁.incl_retr_le (f' (P₀.incl (P₀.retr y))))
      (ScottMap.monotone f' (P₀.incl_retr_le y))

end ScottMapProjection

end DomainTheory.ContinuousLattice
