/-ai
If f and g are Scott continuous, then so is their packing.

A number k lies in the packing at x when either k is 0 and 0 lies in f(x), or k is a successor n + 1 and n lies in g(x). Scott continuity of f or of g supplies a finite piece of x at which the same clause holds, so k lies in the Scott union of the packing. In the other direction, membership at a finite piece of x is carried up to x by monotonicity of f or of g.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem fcapGdeltaPack_isScottContinuous {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fcapGdeltaPack f g) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0⟩ | ⟨n, hk, hn⟩
    · have : 0 ∈ scottUnion f x := by rw [← hf x]; exact h0
      obtain ⟨p, hp, hp0⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inl ⟨hk0, hp0⟩⟩
    · have : n ∈ scottUnion g x := by rw [← hg x]; exact hn
      obtain ⟨p, hp, hnp⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨p, hp, Or.inr ⟨n, hk, hnp⟩⟩
  · intro hk
    obtain ⟨p, hp, h⟩ := mem_scottUnion.mp hk
    rcases h with ⟨hk0, h0⟩ | ⟨n, hk, hn⟩
    · exact Or.inl ⟨hk0, isScottContinuous_monotone hf hp h0⟩
    · exact Or.inr ⟨n, hk, isScottContinuous_monotone hg hp hn⟩

end DomainTheory.DataTypesAsLattices
