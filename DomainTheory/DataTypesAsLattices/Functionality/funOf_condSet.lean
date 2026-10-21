/-ai
Application distributes over the conditional set: applying the conditional of z, x, and y to w equals the conditional of z on the two applications of x and of y to w.

Membership extensionality. A witness for the application lies in one branch of the conditional and reassembles as a witness in that branch after application. Conversely, a branch witness pulls the application witness back into that branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem funOf_condSet (z x y w : Pomega) :
    funOf (condSet z x y) w = condSet z (funOf x w) (funOf y w) := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with ⟨hx, h0⟩ | ⟨hy, ht⟩
    · exact Or.inl ⟨⟨n, hn, hx⟩, h0⟩
    · exact Or.inr ⟨⟨n, hn, hy⟩, ht⟩
  · intro hm
    rcases hm with ⟨⟨n, hn, hx⟩, h0⟩ | ⟨⟨n, hn, hy⟩, ht⟩
    · exact ⟨n, hn, Or.inl ⟨hx, h0⟩⟩
    · exact ⟨n, hn, Or.inr ⟨hy, ht⟩⟩

end DomainTheory.DataTypesAsLattices
