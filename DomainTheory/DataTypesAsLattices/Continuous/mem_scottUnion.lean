/-ai
A natural number k lies in the Scott union of f at x if and only if some code n has its finite set contained in x and has k in f of that finite set.

The Scott union is the union of the Scott pieces. Membership in that union is existence of a piece containing k, and a piece contains k precisely under those two conditions.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem mem_scottUnion {f : Pomega → Pomega} {x : Pomega} {k : ℕ} :
    k ∈ scottUnion f x ↔ ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
  constructor
  · intro hk
    obtain ⟨n, hn, hfk⟩ := Set.mem_iUnion.mp hk
    exact ⟨n, hn, hfk⟩
  · intro ⟨n, hn, hk⟩
    exact Set.mem_iUnion.mpr ⟨n, hn, hk⟩

end DomainTheory.DataTypesAsLattices
