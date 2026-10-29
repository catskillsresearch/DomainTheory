module
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Finset.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
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

theorem retr_eq_sSup (P : IsContinuousLatticeProjection D D') (x' : D') :
    (P.retr : D' → D) x' = sSup {x | (P.incl : D → D') x ≤ x'} := by
  apply le_antisymm
  · exact le_sSup (show (P.incl : D → D') (P.retr x') ≤ x' from P.incl_retr_le x')
  · refine sSup_le fun x hx => ?_
    calc x = (P.retr : D' → D) (P.incl x) := (P.retr_incl x).symm
      _ ≤ (P.retr : D' → D) x' := P.retr.monotone hx

end IsContinuousLatticeProjection
end Proposition310
end DomainTheory.ContinuousLattice
