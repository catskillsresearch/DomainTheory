/-ai
The intersection combinator is combinatory.

The graph of the intersection step equals the interpretation of the closed term interStepTerm, so the closed case of theorem 2.4 makes that graph combinatory. Application of the combinatory fixed-point combinator Y preserves combinatory elements. Theorem 2.5, using Scott continuity of the intersection step, rewrites that application as the intersection combinator.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.interStepTerm
public import DomainTheory.DataTypesAsLattices.Enumeration.interStepTerm_interp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem interC_combinatory : IsCombinatory interC := by
  have hbody : IsCombinatory (graph interStep) := by
    rw [← interStepTerm_interp]
    exact theorem_2_4_closed interStepTerm
  have hfix := IsCombinatory.app Ycomb_combinatory hbody
  rw [theorem_2_5 interStep_isScottContinuous] at hfix
  exact hfix

end DomainTheory.DataTypesAsLattices
