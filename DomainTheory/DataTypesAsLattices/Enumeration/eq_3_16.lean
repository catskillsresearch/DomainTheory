module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_more
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_more
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eq_3_16 (u x : Pomega) :
    funOf Lcomb (barPos u (funOf Rcomb x)) = funOf u x := by
  rw [Lcomb.app, barPos.one, barPos.two, Rcomb.app, seq2.one]

namespace eq_3_16

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem bar (u x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x := by
  rw [barComb.app2, barStepBody, Rcomb.app_zero, eq_2_7_zero]
  exact eq_3_16 u x

theorem operator (u : Pomega) :
    enumComp Lcomb (enumComp (funOf barComb u) Rcomb) =
      graph (fun x => funOf u x) := by
  unfold enumComp
  apply congrArg graph
  funext x
  change funOf Lcomb
    (funOf (lam fun x => funOf (funOf barComb u) (funOf Rcomb x)) x) =
      funOf u x
  rw [beta (theorem_1_3 (funOf.isScottContinuous (funOf barComb u))
      (funOf.isScottContinuous Rcomb)) x]
  exact eq_3_16.bar u x

end eq_3_16

end DomainTheory.DataTypesAsLattices
