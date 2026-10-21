/-ai
The numerical evaluator sends n + 1 to the application of its value at the left unpairing component of n to its value at the right component.

Unfold the evaluator and apply the computation rule for strong recursion.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem valNat_succ (n : ℕ) :
    valNat (n + 1) = valNat (unpair n).1 ⬝ valNat (unpair n).2 := by
  unfold valNat
  rw [Nat.strongRec]

end DomainTheory.DataTypesAsLattices
