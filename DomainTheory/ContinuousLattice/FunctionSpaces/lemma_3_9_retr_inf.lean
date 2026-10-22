module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono_retr

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]


omit [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y] in
/-- **Scott 1972, Lemma 3.9 (retraction at infimum level).** The global equality
`f̄ = j ∘ ḡ` assembles these infimum bounds via Proposition 3.10(i). -/
theorem lemma_3_9_retr_inf {e : X → Y} (P : IsContinuousLatticeProjection D D') {g : X → D'}
    (U : Set Y) :
    P.retr (scottSubspaceExtendInf e g U) ≤ scottSubspaceExtendInf e (fun x => P.retr (g x)) U :=
  scottSubspaceExtendInf_mono_retr (e := e) (g := g) P U

end SubspaceExtension
end DomainTheory.ContinuousLattice
