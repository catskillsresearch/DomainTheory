module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem predSet_succSet (x : Pomega) : predSet (succSet x) = x := by
  ext k
  constructor
  · intro ⟨n, hn, heq⟩
    exact (Nat.succ_injective heq) ▸ hn
  · intro hk
    exact ⟨k, hk, rfl⟩

end DomainTheory.DataTypesAsLattices
