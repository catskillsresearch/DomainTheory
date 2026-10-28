module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.Lambda.topRec
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_16
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem topElem_combinatory : IsCombinatory topElem := by
  have h : funOf Ycomb (interp topRecTerm (fun _ => botElem)) = topElem := by
    rw [topRecTerm.interp, theorem_2_5 topRec.isScottContinuous, eq_2_16]
  exact h ▸ IsCombinatory.app Ycomb.combinatory (theorem_2_4.closed topRecTerm)

end DomainTheory.DataTypesAsLattices
