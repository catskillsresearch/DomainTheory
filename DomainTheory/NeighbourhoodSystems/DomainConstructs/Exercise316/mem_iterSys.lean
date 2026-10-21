/-ai
A set of pairs belongs to the infinite iterate exactly when every fiber is a neighbourhood and, from some index onward, every fiber equals the master.

The identity is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem mem_iterSys {W : Set (ℕ × α)} :
    (iterSys V).mem W ↔ (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master := Iff.rfl

end DomainTheory.NeighbourhoodSystems
