module
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]
variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

theorem lemma_3_9_retr_inf {e : X → Y} (P : ContinuousLatticeProjection D D') {g : X → D'}
    (U : Set Y) :
    P.retr (scottSubspaceExtend.inf e g U) ≤ scottSubspaceExtend.inf e (fun x => P.retr (g x)) U :=
  scottSubspaceExtend.inf_mono_retr (e := e) (g := g) P U

end DomainTheory.ContinuousLattice
