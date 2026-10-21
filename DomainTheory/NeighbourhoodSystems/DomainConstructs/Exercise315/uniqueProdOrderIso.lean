/-ai
When the first factor has a unique element, projection to the second factor is an order isomorphism from the product onto that factor, with inverse pairing the default with an element. The left inverse uses that every first component equals the default, and product order reduces to order of the second components because any two first components are equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- For a `Unique` first factor, `C × A ≃o A` (forget the constant component). -/
def uniqueProdOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : C × A ≃o A where
  toFun p := p.2
  invFun a := (default, a)
  left_inv p := by
    have : (default : C) = p.1 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨c, a⟩ ⟨c', a'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨le_of_eq (Subsingleton.elim c c'), h⟩, And.right⟩

end DomainTheory.NeighbourhoodSystems
