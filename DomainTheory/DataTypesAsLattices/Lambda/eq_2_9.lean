module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_9 (f g x : Pomega) :
    funOf (f ∪ g) x = funOf f x ∪ funOf g x := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨n, hn, hp⟩
    · exact Or.inr ⟨n, hn, hp⟩
  · intro h
    rcases h with ⟨n, hn, hp⟩ | ⟨n, hn, hp⟩
    · exact ⟨n, hn, Or.inl hp⟩
    · exact ⟨n, hn, Or.inr hp⟩

end DomainTheory.DataTypesAsLattices
