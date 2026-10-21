/-ai
Application of the top element to any argument is the top element.

Membership extensionality. One direction is immediate. The other uses the witness 0, which lies in the zero finite element, together with the trivial membership in the top element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



theorem funOf_top (x : Pomega) : funOf topElem x = topElem := by
  ext m
  constructor
  · intro
    trivial
  · intro
    exact ⟨0, by simp [e_zero], trivial⟩

end DomainTheory.DataTypesAsLattices
