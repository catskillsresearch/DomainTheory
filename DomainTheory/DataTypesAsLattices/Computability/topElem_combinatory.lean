/-ai
The top element of Pω is combinatory.

The fixed-point combinator applied to the interpretation of topRecTerm in the constantly bottom environment equals the top element, by topRecTerm_interp, the fixed-point theorem theorem_2_5 for the Scott-continuous map topRec, and equation eq_2_16. Rewriting by this equality exhibits the top element as the application of the combinatory fixed-point combinator to the combinatory closed term topRecTerm.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem topElem_combinatory : IsCombinatory topElem := by
  have h : funOf Ycomb (interp topRecTerm (fun _ => botElem)) = topElem := by
    rw [topRecTerm_interp, theorem_2_5 topRec_isScottContinuous, eq_2_16]
  exact h ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed topRecTerm)

end DomainTheory.DataTypesAsLattices
