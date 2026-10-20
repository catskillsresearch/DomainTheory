module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






theorem eq_5_10 (x y : Pomega) : squareSnd (squarePair x y) = y := by
  ext m
  constructor
  · intro hm
    rcases hm with ⟨n, _, h⟩ | ⟨k, hk, h⟩
    · omega
    · have : k = m := by omega
      simpa [this] using hk
  · intro hm
    exact Or.inr ⟨m, hm, rfl⟩

end DomainTheory.DataTypesAsLattices
