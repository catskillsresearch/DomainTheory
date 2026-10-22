/-ai
The identity combinator is contained in the graph of a map f if and only if f is expansive on every finite set en.

A pair (n, m) lies in the identity when m lies in en, and it lies in the graph of f when m lies in f(en). Pairing codes are injective, so the two containment statements describe the same pairs.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Graph expansiveness `I ⊆ λx. f(x)` is value-expansiveness on finite sets. -/
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
