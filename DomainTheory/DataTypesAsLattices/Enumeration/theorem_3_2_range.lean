module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































/-- **Scott 1976, Theorem 3.2.** `RE` is exactly the range of `val`. -/
theorem theorem_3_2_range : RE = Set.range valNat := by
  ext u
  constructor
  · intro hu
    exact theorem_3_2_surjective hu
  · intro ⟨n, hn⟩
    simpa [← hn] using (theorem_3_2).1 n

end DomainTheory.DataTypesAsLattices
