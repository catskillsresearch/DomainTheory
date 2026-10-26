module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more
public import DomainTheory.DataTypesAsLattices.Computability.SK_comp
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Primitive recursion with zero initial value, viewed as an operator on its step. -/
def primRecZeroC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ dollarC) ⬝
    (Scomb ⬝ (Kcomb ⬝ Ycomb) ⬝
      (interp primRecStepTerm (fun _ => botElem) ⬝ ofNat 0))

namespace primRecZeroC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem app (f : Pomega) :
    primRecZeroC ⬝ f = primRecComb (ofNat 0) f := by
  rw [primRecZeroC, SK_comp, SK_comp]
  rfl


theorem combinatory : IsCombinatory primRecZeroC :=
  .app (.app .S (.app .K dollarC.combinatory))
    (.app (.app .S (.app .K Ycomb.combinatory))
      (.app (theorem_2_4.closed primRecStepTerm) (ofNat.combinatory 0)))

end primRecZeroC

end DomainTheory.DataTypesAsLattices
