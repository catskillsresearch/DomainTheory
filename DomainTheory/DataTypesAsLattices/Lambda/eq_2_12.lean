/-ai
Scott 1976, (2.12). Abstraction distributes over intersection: the intersection of the graphs of τ and σ is the graph of their pointwise intersection.

A pair code in both graphs has the same components by injectivity of pairing, and the value lies in both results. A pair code whose value lies in both results lies in both graphs.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.12).** Abstraction distributes over intersection. -/
theorem eq_2_12 (τ σ : Pomega → Pomega) :
    graph τ ∩ graph σ = graph (fun x => τ x ∩ σ x) := by
  ext p
  constructor
  · intro ⟨hτ, hσ⟩
    rcases hτ with ⟨n, m, hpτ, hmτ⟩
    rcases hσ with ⟨n', m', hpσ, hmσ⟩
    have hp' : pair n m = pair n' m' := hpτ.symm.trans hpσ
    obtain ⟨rfl, rfl⟩ := pair_inj hp'
    exact ⟨n, m, hpτ, hmτ, hmσ⟩
  · intro h
    rcases h with ⟨n, m, hp, hmτ, hmσ⟩
    exact ⟨⟨n, m, hp, hmτ⟩, ⟨n, m, hp, hmσ⟩⟩

end DomainTheory.DataTypesAsLattices
