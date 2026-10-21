/-ai
If an element u is generated from G, then applying the bar combinator to u lies in the generated semigroup.

Induct on the generation of u. The generator G is the bar generator of the semigroup. At an application, rewrite by equation (3.17) read from right to left, and form the semigroup composite of the first inductive image with the composite of the second inductive image and R.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code




















































theorem bar_generated {u : Pomega} (hu : GeneratedFromG u) :
    GeneratedSemigroup (funOf barComb u) := by
  induction hu with
  | G => exact GeneratedSemigroup.Gbar
  | app _ _ ihu ihv =>
      rw [← eq_3_17]
      exact .comp ihu (.comp ihv .R)

end DomainTheory.DataTypesAsLattices
