/-ai
The bar step body of B, u, and x is the conditional on the application of x to the numeral 0. Its first branch is the positive bar branch of u and x, and its second branch applies B to the application of u to the application of x to the numeral 1, and then to the application of x to the numeral 2. This is the step of the bar operator in Scott 1976, (3.15).
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Scott 1976, (3.15).** Step of `ū = λx. x₀ ⊃ ⟨1, u, x₁⟩, overline{u(x₁)(x₂)}`. -/
def barStepBody (B u x : Pomega) : Pomega :=
  condSet (funOf x (ofNat 0)) (barPos u x)
    (funOf (funOf B (funOf u (funOf x (ofNat 1)))) (funOf x (ofNat 2)))

end DomainTheory.DataTypesAsLattices
