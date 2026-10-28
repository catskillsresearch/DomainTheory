
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Icomb_subset_graph {f : Pomega → Pomega} :
    Icomb ⊆ graph f ↔ ∀ n, e n ⊆ f (e n) := by
  constructor
  · intro h n m hm
    have := h ⟨n, m, rfl, hm⟩
    rcases this with ⟨n', m', heq, hm'⟩
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact hm'
  · intro h p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, h n hm⟩

end DomainTheory.DataTypesAsLattices
