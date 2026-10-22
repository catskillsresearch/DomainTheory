/-ai
The predecessor of the successor of a set of natural numbers is the set itself.

If a number lies in the predecessor of the successor, some member of the set has that number as its successor, and injectivity of the successor forces the member to be the number. Conversely, a member of the set is a witness that it lies in the predecessor of the successor.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
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
