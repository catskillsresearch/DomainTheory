/-ai
The operator component of the pair of natural numbers n and m is n.

Simplify by the definition of the operator component and by unpairing a pair.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem eq_3_5 (n m : ℕ) : opNat (pair n m) = n := by simp [opNat, unpair_pair]
end DomainTheory.DataTypesAsLattices
