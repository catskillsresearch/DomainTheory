module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_app
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.not_mem_zero_Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack_ne_bot

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.8).** `G(G) = 0`. -/
theorem Gcomb_app_self : funOf Gcomb Gcomb = zeroC := by
  have hne : Gcomb ≠ botElem := by
    intro h
    have : Gpack = funOf botElem (ofNat 0) := by
      have := congrArg (fun w => funOf w (ofNat 0)) h
      simpa [Gcomb_zero] using this
    have hbot : funOf botElem (ofNat 0) = botElem := by
      ext; simp [funOf, botElem]
    exact Gpack_ne_bot (this.trans hbot)
  rw [Gcomb_app]
  exact eq_2_7_pos Gpack zeroC Gcomb not_mem_zero_Gcomb hne

end DomainTheory.DataTypesAsLattices
