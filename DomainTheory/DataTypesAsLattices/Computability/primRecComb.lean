module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStepTerm
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.primRecHat
public import DomainTheory.DataTypesAsLattices.Lambda.primRecVal
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_27
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Scott (2.27) packaged as a combinator. -/
def primRecComb (a f : Pomega) : Pomega :=
  funOf dollarC
    (funOf Ycomb
      (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f))

namespace primRecComb

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory {a f : Pomega}
    (ha : IsCombinatory a) (hf : IsCombinatory f) :
    IsCombinatory (primRecComb a f) :=
  .app dollarC.combinatory <|
    .app Ycomb.combinatory <|
      .app (.app (theorem_2_4.closed primRecStepTerm) ha) hf

theorem ofNat (a f : Pomega) (n : ℕ) :
    funOf (primRecComb a f) (_root_.DomainTheory.DataTypesAsLattices.ofNat n) =
      primRecVal a f n := by
  have hgraph := primRecStep.graph_of a f
  have hfix := theorem_2_5 (primRecStep.isScottContinuous a f)
  simp only [primRecComb]
  rw [← hgraph, hfix, ← _root_.DomainTheory.DataTypesAsLattices.eq_2_27,
    primRecHat.ofNat]

end primRecComb

end DomainTheory.DataTypesAsLattices
