/-ai
G-bar belongs to the set of functional elements.

Membership is the equation that G-bar equals the graph of its own application. Equation 3.15 writes G-bar as the graph of the bar-step body of the bar combinator at G, that body is Scott continuous in the remaining argument, and rewriting by this representation and by Theorem 1.2(i) yields the equation.
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


theorem Gbar_mem_FUN : Gbar ∈ FUN := by
  change Gbar = graph (funOf Gbar)
  have h : Gbar = graph (fun x => barStepBody barComb Gcomb x) := eq_3_15 Gcomb
  have hf : IsScottContinuous (fun x => barStepBody barComb Gcomb x) :=
    barStepBody_isScottContinuous_x barComb Gcomb
  rw [h, theorem_1_2_i hf]

end DomainTheory.DataTypesAsLattices
