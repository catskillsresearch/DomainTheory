/-ai
The packed combinator is distinct from bottom.

If it were bottom, applying both sides to the numeral 0 and using the left projection of a pair sequence would make successor equal the application of bottom at that numeral. The number 1 lies in the application of successor to the numeral 0, and simplifying the application of bottom contradicts that membership.
ai-/
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

theorem Gpack_ne_bot : Gpack ≠ botElem := by
  intro h
  have hs : sucC = funOf botElem (ofNat 0) := by
    have := congrArg (fun w => funOf w (ofNat 0)) h
    simpa [Gpack, seq2_app_zero] using this
  have h1 : (1 : ℕ) ∈ funOf sucC (ofNat 0) := by
    rw [sucC_app]; exact ⟨0, rfl, rfl⟩
  rw [hs] at h1
  simp [funOf, botElem] at h1

end DomainTheory.DataTypesAsLattices
