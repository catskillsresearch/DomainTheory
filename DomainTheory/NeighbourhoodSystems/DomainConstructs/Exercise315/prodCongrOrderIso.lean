module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- The product of two order isomorphisms, as an order isomorphism. -/
def prodCongrOrderIso {A B C D : Type*} [Preorder A] [Preorder B] [Preorder C] [Preorder D]
    (e₀ : A ≃o B) (e₁ : C ≃o D) : A × C ≃o B × D where
  toFun p := (e₀ p.1, e₁ p.2)
  invFun q := (e₀.symm q.1, e₁.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    show (e₀ a, e₁ c) ≤ (e₀ a', e₁ c') ↔ (a, c) ≤ (a', c')
    rw [Prod.mk_le_mk, Prod.mk_le_mk, e₀.le_iff_le, e₁.le_iff_le]

end DomainTheory.NeighbourhoodSystems
