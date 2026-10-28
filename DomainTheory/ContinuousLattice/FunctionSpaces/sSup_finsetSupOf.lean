module

public import DomainTheory.ContinuousLattice.FunctionSpaces.finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_le_finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_sSup_finsetSupOf
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Proposition310

open Finset

namespace IsContinuousLatticeProjection

theorem sSup_finsetSupOf (S : Set D) : sSup S = sSup (finsetSupOf S) :=
  le_antisymm (le_sSup_finsetSupOf S) (sSup_le_finsetSupOf S)

end IsContinuousLatticeProjection

end Proposition310

end DomainTheory.ContinuousLattice
