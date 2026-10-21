/-ai
Every value of the environment primRecOpEnv is combinatory.

At index 2 the value is combinatory by dollarC_combinatory, at index 3 by Ycomb_combinatory, and at index 4 by theorem_2_4_closed applied to primRecStepTerm. At indices 0 and 1, and at every index of the form n + 5, it is combinatory by botElem_combinatory.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.botElem_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem primRecOpEnv_combinatory : ∀ i, IsCombinatory (primRecOpEnv i)
  | 2 => dollarC_combinatory
  | 3 => Ycomb_combinatory
  | 4 => theorem_2_4_closed primRecStepTerm
  | 0 | 1 => botElem_combinatory
  | _ + 5 => botElem_combinatory

end DomainTheory.DataTypesAsLattices
