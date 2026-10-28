module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_sqrt
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sqrtC : Pomega :=
  Scomb ⬝
    (Scomb ⬝ (Kcomb ⬝ primRecZeroC) ⬝ sqrtStepC) ⬝
    (Scomb ⬝ Kcomb ⬝ Kcomb)

namespace sqrtC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : IsCombinatory sqrtC :=
  .app
    (.app .S
      (.app (.app .S (.app .K primRecZeroC.combinatory))
        sqrtStepC.combinatory))
    (.app (.app .S .K) .K)

theorem realizes : Realizes sqrtC Nat.sqrt := fun n => by
  rw [sqrtC, Scomb.beta3, Scomb.beta3, Scomb.beta3, Kcomb.beta2, Kcomb.beta2,
    primRecZeroC.app, primRecComb.ofNat,
    primRecVal_sqrt, sqrtIter.self]

end sqrtC

end DomainTheory.DataTypesAsLattices
