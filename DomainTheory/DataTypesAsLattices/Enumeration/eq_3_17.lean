module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eq_3_17 (u v : Pomega) :
    enumComp (funOf barComb u) (enumComp (funOf barComb v) Rcomb) =
      funOf barComb (funOf u v) := by
  conv_rhs => rw [eq_3_15]
  unfold enumComp
  apply congrArg graph
  funext x
  change funOf (funOf barComb u)
    (funOf (lam fun x => funOf (funOf barComb v) (funOf Rcomb x)) x) =
      barStepBody barComb (funOf u v) x
  rw [beta (theorem_1_3 (funOf.isScottContinuous (funOf barComb v))
      (funOf.isScottContinuous Rcomb)) x]
  rw [barComb.on_R, barComb.on_barPos_R, barComb.app2]

namespace eq_3_17

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem projections (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x := by
  refine ⟨barPos.one _ _, barPos.one _ _, ?_⟩
  rw [barPos.two, Rcomb.app, seq2.one]

theorem semigroup (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf Lcomb (barPos (funOf u v) (funOf Rcomb x)) =
        funOf (funOf u v) x :=
  ⟨(eq_3_17.projections u v x).1, eq_3_16 (funOf u v) x⟩

end eq_3_17

end DomainTheory.DataTypesAsLattices
