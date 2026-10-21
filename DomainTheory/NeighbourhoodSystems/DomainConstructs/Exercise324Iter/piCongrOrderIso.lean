/-ai
A family of order isomorphisms, one at each index, induces an order isomorphism of the dependent products by applying the isomorphism at each coordinate and inverting by the inverse at each coordinate. The two directions cancel pointwise, and a pointwise inequality is an inequality at each coordinate, which each isomorphism preserves and reflects.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A pointwise family of order-isomorphisms induces one on the dependent product. -/
def piCongrOrderIso {ι : Type*} {A B : ι → Type*} [∀ i, Preorder (A i)] [∀ i, Preorder (B i)]
    (e : ∀ i, A i ≃o B i) : (∀ i, A i) ≃o (∀ i, B i) where
  toFun f := fun i => e i (f i)
  invFun g := fun i => (e i).symm (g i)
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp
  map_rel_iff' := by
    intro f g
    exact ⟨fun h i => (e i).le_iff_le.mp (h i), fun h i => (e i).le_iff_le.mpr (h i)⟩

end DomainTheory.NeighbourhoodSystems
