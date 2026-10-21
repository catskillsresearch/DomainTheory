/-ai
Applying G to the numeral of k + 1 returns zero.

Rewrite by the application law for G and by the successor clause of the conditional.
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


theorem Gcomb_succ (k : ℕ) : funOf Gcomb (ofNat (k + 1)) = zeroC := by
  rw [Gcomb_app, eq_2_7_succ]

end DomainTheory.DataTypesAsLattices
