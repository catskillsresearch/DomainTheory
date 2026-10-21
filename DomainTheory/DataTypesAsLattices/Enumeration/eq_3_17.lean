/-ai
Scott 1976, (3.17): composing the bar of u with the composition of the bar of v and R yields the bar of the application of u to v.

Rewrite the right side by the unfolding (3.15), unfold composition, and compare graphs. At an element x, beta reduction applies by the substitution theorem, composing continuity of application of the bar of v with continuity of application of R. Rewrite the resulting application by the action of the bar on R, the action of the bar on a positive branch at R, and the two-argument application of the bar.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_on_R
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_on_barPos_R

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































/-- **Scott 1976, (3.17).** Operator identity
`ū ∘ v̄ ∘ R = overline{u(v)}`. -/
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
  rw [beta (theorem_1_3 (funOf_isScottContinuous (funOf barComb v))
      (funOf_isScottContinuous Rcomb)) x]
  rw [barComb_on_R, barComb_on_barPos_R, barComb_app2]

end DomainTheory.DataTypesAsLattices
