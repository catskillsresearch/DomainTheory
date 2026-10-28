module

public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.con_
public import DomainTheory.ContinuousLattice.FunctionSpaces.min
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace Proposition313

noncomputable def projection : IsContinuousLatticeProjection D (ScottMap D D) where
  incl := con
  retr := min
  retr_incl := fun _ => rfl
  incl_retr_le := fun f => by
    rw [ScottMap.le_def]
    intro y
    show ((ScottMap.const ((f : D → D) ⊥) : ScottMap D D) : D → D) y ≤ (f : D → D) y
    rw [ScottMap.const_apply]
    exact f.monotone bot_le

end Proposition313

end DomainTheory.ContinuousLattice
