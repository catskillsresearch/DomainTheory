/-ai
The combinator G is recursively enumerable.

Apply the lemma that every combinatory element is recursively enumerable to the fact that G is combinatory.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem Gcomb_isRE : IsRE Gcomb :=
  combinatory_isRE Gcomb_combinatory

end DomainTheory.DataTypesAsLattices
