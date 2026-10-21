/-ai
The shift is an order isomorphism from sequences in a preorder to the product of that preorder with the sequences: a sequence is sent to its value at zero paired with its tail, and a pair is sent back by cases on zero and successor. The left inverse is by cases on the index, the right inverse is reflexive, and order is preserved and reflected by splitting a pointwise inequality into the value at zero and the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_component

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The shift order-isomorphism `(ℕ → E) ≃o E × (ℕ → E)`, `f ↦ (f 0, f ∘ succ)`. -/
def natShiftEquiv (E : Type*) [Preorder E] : (ℕ → E) ≃o E × (ℕ → E) where
  toFun f := (f 0, fun n => f (n + 1))
  invFun p := fun n => Nat.casesOn n p.1 (fun m => p.2 m)
  left_inv f := by funext n; cases n <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h0, hs⟩
      intro n
      cases n with
      | zero => exact h0
      | succ m => exact hs m
    · intro h
      exact ⟨h 0, fun m => h (m + 1)⟩

end DomainTheory.NeighbourhoodSystems
