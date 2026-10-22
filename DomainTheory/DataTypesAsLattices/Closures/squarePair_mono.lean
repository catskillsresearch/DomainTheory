module

public import Mathlib.Algebra.Ring.Parity
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
