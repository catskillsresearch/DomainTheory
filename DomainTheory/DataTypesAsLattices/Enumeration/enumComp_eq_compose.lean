/-ai
Composition of u and v equals the function retract applied to the composition combinator of u and v.

Rewrite by the application law for the retract and the definition of the composition combinator, compare graphs, and at an element x use the symmetric SK composition identity.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem enumComp_eq_compose (u v : Pomega) :
    enumComp u v = funOf funRetract (composeC u v) := by
  rw [funRetract_app, composeC]
  apply congrArg graph
  funext x
  exact (SK_comp u v x).symm

end DomainTheory.DataTypesAsLattices
