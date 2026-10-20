module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
