/-ai
For any function v, the recursion code of n equals the application of v(n) to the numeral of v(n).

This is the definition of the recursion code.
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


theorem theorem_3_3_ii (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := rfl

end DomainTheory.DataTypesAsLattices
