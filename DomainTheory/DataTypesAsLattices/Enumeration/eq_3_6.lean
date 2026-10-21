/-ai
The argument component of the pair of natural numbers n and m is m.

Simplify by the definition of the argument component and by unpairing a pair.
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






























theorem eq_3_6 (n m : ℕ) : argNat (pair n m) = m := by simp [argNat, unpair_pair]

end DomainTheory.DataTypesAsLattices
