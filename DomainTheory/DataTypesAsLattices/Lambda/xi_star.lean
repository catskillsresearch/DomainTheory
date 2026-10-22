module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Table 1 (ξ*).** Abstraction is monotone. -/
theorem xi_star {τ σ : Pomega → Pomega} (h : ∀ x, τ x ⊆ σ x) :
    graph τ ⊆ graph σ := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, h _ hm⟩

end DomainTheory.DataTypesAsLattices
