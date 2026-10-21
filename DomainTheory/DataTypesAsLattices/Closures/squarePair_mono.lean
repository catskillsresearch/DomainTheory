/-ai
Disjoint pairing is monotone in each argument.

An even member remains even because its first component is carried into the larger first set, and an odd member remains odd because its second component is carried into the larger second set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem squarePair_mono {x x' y y' : Pomega} (hx : x ⊆ x') (hy : y ⊆ y') :
    squarePair x y ⊆ squarePair x' y' := by
  intro k hk
  rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
  · exact Or.inl ⟨n, hx hn, hk⟩
  · exact Or.inr ⟨m, hy hm, hk⟩

end DomainTheory.DataTypesAsLattices
