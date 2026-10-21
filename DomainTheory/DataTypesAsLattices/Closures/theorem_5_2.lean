/-ai
Scott's representation theorem says that the representing closure of a countably algebraic lattice is Scott continuous, that its code is a closure operation, and that the lattice is in bijection with the fixed points of that code by a map which preserves and reflects inclusion.

Scott continuity and the closure property are the corresponding theorems for the representing closure. The bijection is the representation order isomorphism, and each direction of the inclusion correspondence is the corresponding direction of that isomorphism's relation law.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode_isClosure

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.2 (The representation theorem).**
The constructed code is a continuous closure operation and its fixed-point
range is order-isomorphic to the source lattice. -/
theorem theorem_5_2 {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) ∧
      IsClosure (representClosureCode D) ∧
      ∃ φ : α → Fixpoints (funOf (representClosureCode D)),
        Function.Bijective φ ∧
          ∀ x y, x ≤ y ↔ (φ x : Pomega) ⊆ φ y :=
  ⟨representClosure_isScottContinuous D,
    representClosureCode_isClosure D,
    ⟨fun x => representationOrderIso D x,
      (representationOrderIso D).toEquiv.bijective,
      fun x y => by
        constructor
        · intro hxy
          exact (representationOrderIso D).map_rel_iff.mpr hxy
        · intro hsub
          exact (representationOrderIso D).map_rel_iff.mp hsub⟩⟩

end DomainTheory.DataTypesAsLattices
