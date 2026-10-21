/-ai
The bar combinator is combinatory.

Interpreting the bar step term in the constantly bottom environment and applying the Y combinator recovers the bar combinator, by that interpretation together with the first recursion theorem for the Scott-continuous bar step. Substituting the equality, the bar combinator is an application of the combinatory Y combinator to the combinatory interpretation of the closed bar step term given by theorem 2.4.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepTerm_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.barStep_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barComb_combinatory : IsCombinatory barComb := by
  have hY : funOf Ycomb (interp barStepTerm (fun _ => botElem)) = barComb := by
    rw [barStepTerm_interp, theorem_2_5 barStep_isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed barStepTerm)

end DomainTheory.DataTypesAsLattices
