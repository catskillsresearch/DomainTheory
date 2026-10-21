/-ai
Scott 1976, (2.10). Abstraction distributes over union: the union of the graphs of τ and σ is the graph of their pointwise union.

A pair code in either graph is a pair code whose value lies in the corresponding disjunct, and a pair code whose value lies in one disjunct lies in the corresponding graph.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.10).** Abstraction distributes over union. -/
theorem eq_2_10 (τ σ : Pomega → Pomega) :
    graph τ ∪ graph σ = graph (fun x => τ x ∪ σ x) := by
  ext p
  constructor
  · intro hp
    rcases hp with h | h
    · rcases h with ⟨n, m, hp, hm⟩
      exact ⟨n, m, hp, Or.inl hm⟩
    · rcases h with ⟨n, m, hp, hm⟩
      exact ⟨n, m, hp, Or.inr hm⟩
  · intro h
    rcases h with ⟨n, m, hp, hm⟩
    rcases hm with hm | hm
    · exact Or.inl ⟨n, m, hp, hm⟩
    · exact Or.inr ⟨n, m, hp, hm⟩

end DomainTheory.DataTypesAsLattices
