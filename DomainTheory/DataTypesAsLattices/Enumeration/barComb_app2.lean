/-ai
Applying the bar combinator to u and then to x yields the bar step body at the bar combinator, u, and x.

Equation (3.15) says that applying the bar combinator to u is the graph of the bar step body in its third argument. Beta reduction, using Scott continuity of that body in x, evaluates the graph at x.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody_isScottContinuous_x
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barComb_app2 (u x : Pomega) :
    funOf (funOf barComb u) x = barStepBody barComb u x := by
  have ha : funOf barComb u = graph (fun z => barStepBody barComb u z) :=
    eq_3_15 u
  rw [ha]
  exact beta (barStepBody_isScottContinuous_x barComb u) x

end DomainTheory.DataTypesAsLattices
