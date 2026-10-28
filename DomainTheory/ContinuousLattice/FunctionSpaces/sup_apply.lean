module

public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

theorem sup_apply (f g : ScottMap D D') (x : D) :
    ((f ⊔ g : ScottMap D D') : D → D') x = f x ⊔ g x := by
  have h : (f ⊔ g : ScottMap D D') = sSup ({f, g} : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_pair]
  exact sSup_pair

end ScottMap

end DomainTheory.ContinuousLattice
