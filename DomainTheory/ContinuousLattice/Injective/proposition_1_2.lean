/-ai
The Sierpiński space is injective.

This is the injectivity of the space of propositions.
ai-/
module

public import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski

@[expose] public section


theorem proposition_1_2 : IsInjectiveSpace.{u} Sierpinski :=
  isInjectiveSpace_sierpinski
