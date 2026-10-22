/-ai
Composing L with the composition of the bar combinator of u and R yields the graph of application of u.

Unfold composition and compare graphs. At an element x the goal is an application of L to a lambda applied to x. Beta reduction applies by the substitution theorem, composing continuity of application of the bar combinator of u with continuity of application of R, and equation (3.16) for the bar combinator gives the pointwise equality.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16_bar

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem eq_3_16_operator (u : Pomega) :
    enumComp Lcomb (enumComp (funOf barComb u) Rcomb) =
      graph (fun x => funOf u x) := by
  unfold enumComp
  apply congrArg graph
  funext x
  change funOf Lcomb
    (funOf (lam fun x => funOf (funOf barComb u) (funOf Rcomb x)) x) =
      funOf u x
  rw [beta (theorem_1_3 (funOf_isScottContinuous (funOf barComb u))
      (funOf_isScottContinuous Rcomb)) x]
  exact eq_3_16_bar u x

end DomainTheory.DataTypesAsLattices
