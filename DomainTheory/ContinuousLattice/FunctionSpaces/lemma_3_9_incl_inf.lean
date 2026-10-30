module
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]
variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

theorem lemma_3_9_incl_inf {e : X → Y} (P : ContinuousLatticeProjection D D')
    {f : X → D} {g : X → D'} (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    P.incl (scottSubspaceExtend.inf e f U) ≤ scottSubspaceExtend.inf e g U :=
  le_trans (scottSubspaceExtend.inf_mono_incl_apply (e := e) (f := f) U P)
    (scottSubspaceExtend.inf_mono_incl (e := e) (f := f) (g := g) P hfg U)

end DomainTheory.ContinuousLattice
