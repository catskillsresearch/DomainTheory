/-ai
Scott 1976, (2.11). Application of an intersection is contained in the intersection of the applications. Equality needs both arguments to be graphs.

A finite set contained in the argument whose pair code lies in both sets witnesses membership in each of the two applications.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























/-- **Scott 1976, (2.11).** One inclusion; equality needs both arguments to be graphs. -/
theorem eq_2_11 (f g x : Pomega) :
    funOf (f ∩ g) x ⊆ funOf f x ∩ funOf g x := by
  intro m ⟨n, hn, hp, hq⟩
  exact ⟨⟨n, hn, hp⟩, ⟨n, hn, hq⟩⟩

end DomainTheory.DataTypesAsLattices
