/-ai
The composition of two combinatory elements is combinatory.

Rewrite composition as the application of the function retract to the composition combinator of the two elements. The retract is combinatory, and the composition combinator of two combinatory elements is combinatory.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.funRetract_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp_eq_compose

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem enumComp_combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (enumComp u v) := by
  rw [enumComp_eq_compose]
  exact .app funRetract_combinatory (composeC_combinatory hu hv)

end DomainTheory.DataTypesAsLattices
