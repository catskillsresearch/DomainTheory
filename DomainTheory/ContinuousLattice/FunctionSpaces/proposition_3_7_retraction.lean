module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- **Scott 1972, Proposition 3.7 (retraction).** Function spaces inherit retractions. -/
def proposition_3_7_retraction (R₀ : IsContinuousLatticeRetraction D₀ D₀')
    (R₁ : IsContinuousLatticeRetraction D₁ D₁') :
    ScottMapRetraction D₀ D₀' D₁ D₁' :=
  ScottMapRetraction.functionSpace R₀ R₁

end DomainTheory.ContinuousLattice
