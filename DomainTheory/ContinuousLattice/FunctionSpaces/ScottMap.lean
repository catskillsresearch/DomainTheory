module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

def ScottMap (D : Type u) (D' : Type v) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

end ScottMap

end DomainTheory.ContinuousLattice
