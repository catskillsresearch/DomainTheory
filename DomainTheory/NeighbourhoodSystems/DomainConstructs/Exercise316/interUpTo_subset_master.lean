/-ai
In the infinite iterate, the intersection of the first N members of a family of neighbourhoods is contained in the master neighbourhood.

Proceed by induction on N. The zero case is reflexive. At a successor, rewrite the successor intersection and compose the inclusion of an intersection into its left factor with the inductive inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem interUpTo_subset_master (F : ℕ → Set (ℕ × α)) (N : ℕ) :
    (iterSys V).interUpTo F N ⊆ (iterSys V).master := by
  induction N with
  | zero => exact subset_rfl
  | succ n ih => rw [NeighborhoodSystem.interUpTo_succ]; exact Set.inter_subset_left.trans ih

end DomainTheory.NeighbourhoodSystems
