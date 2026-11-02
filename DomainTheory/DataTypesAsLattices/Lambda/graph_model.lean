module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem xi_star {τ σ : Pomega → Pomega} (h : ∀ x, τ x ⊆ σ x) :
    graph τ ⊆ graph σ := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, h _ hm⟩

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
