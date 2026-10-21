/-ai
Scott 1976, Table 1 (ξ*). Abstraction is monotone. If τ(x) is contained in σ(x) for every x, then the graph of τ is contained in the graph of σ.

A code in the graph of τ is a pair (n, m) with m in τ of the finite set coded by n. The hypothesis puts m in σ of that same finite set, so the pair lies in the graph of σ.
ai-/
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
