module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.1 (The generator theorem).**
All LAMBDA-definable elements are obtained from `G` by iterated application. -/
theorem sucC_zero : funOf sucC zeroC = ofNat 1 := by
  rw [sucC_app]
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    simp [zeroC, ofNat] at hn
    subst hn
    simpa [ofNat] using hk
  · intro hk
    simp [ofNat] at hk
    exact ⟨0, rfl, hk⟩

end DomainTheory.DataTypesAsLattices
