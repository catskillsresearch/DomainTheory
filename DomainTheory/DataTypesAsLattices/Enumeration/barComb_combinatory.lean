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
