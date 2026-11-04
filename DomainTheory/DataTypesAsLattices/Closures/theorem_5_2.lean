module

public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
import DomainTheory.DataTypesAsLattices.Closures.representationOrderIso
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_2 {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) ∧
      Closure (representClosureCode D) ∧
      ∃ φ : α → Fixpoints (funOf (representClosureCode D)),
        Function.Bijective φ ∧
          ∀ x y, x ≤ y ↔ (φ x : Pomega) ⊆ φ y :=
  ⟨representClosure.isScottContinuous D,
    representClosureCode.isClosure D,
    ⟨fun x => representationOrderIso D x,
      (representationOrderIso D).toEquiv.bijective,
      fun x y => by
        constructor
        · intro hxy
          exact (representationOrderIso D).map_rel_iff.mpr hxy
        · intro hsub
          exact (representationOrderIso D).map_rel_iff.mp hsub⟩⟩

end DomainTheory.DataTypesAsLattices
