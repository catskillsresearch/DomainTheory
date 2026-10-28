module

public import DomainTheory.ContinuousLattice.FunctionSpaces.finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.mem_finsetSupOf_of_mem
public import Mathlib.Order.BourbakiWitt
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

theorem le_sSup_finsetSupOf (S : Set D) : sSup S ≤ sSup (finsetSupOf S) :=
  sSup_le fun _ hx => le_sSup (mem_finsetSupOf_of_mem hx)

end IsContinuousLatticeProjection

end Proposition310

end DomainTheory.ContinuousLattice
