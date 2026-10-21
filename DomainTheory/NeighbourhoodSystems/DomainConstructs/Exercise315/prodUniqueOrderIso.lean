/-ai
When the second factor has a unique element, projection to the first factor is an order isomorphism from the product onto that factor, with inverse pairing an element with the default. The left inverse uses that every second component equals the default, and product order reduces to order of the first components because any two second components are equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- For a `Unique` second factor, `A × C ≃o A` (forget the constant component). -/
def prodUniqueOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : A × C ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := by
    have : (default : C) = p.2 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨h, le_of_eq (Subsingleton.elim c c')⟩, And.left⟩

end DomainTheory.NeighbourhoodSystems
