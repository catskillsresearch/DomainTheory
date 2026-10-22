module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise314.diag

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


@[simp] theorem diag_rel {Z : Set α} {P : Set (α ⊕ α)} :
    (diag V).rel Z P ↔
      (prod V V).mem P ∧ (idMap V).rel Z (Sum.inl ⁻¹' P) ∧ (idMap V).rel Z (Sum.inr ⁻¹' P) :=
  Iff.rfl

@[simp] theorem toElementMap_diag (x : V.Element) :
    (diag V).toElementMap x = pair x x := by
  rw [diag, toElementMap_paired, toElementMap_idMap]
end DomainTheory.NeighbourhoodSystems
