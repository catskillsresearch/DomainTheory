module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.Projections
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_sSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

namespace Projections

noncomputable instance instSupSet : SupSet (Projections D) :=
  ⟨fun T => ⟨sSup (Set.image Subtype.val T), isProjection_sSup (by rintro j ⟨p, _, rfl⟩; exact p.2)⟩⟩

end Projections

end Projections

end DomainTheory.ContinuousLattice
