/-ai
The numerical evaluator sends the filter-operator code to the filter combinator.

The equality is the specification of the witness chosen by the surjectivity clause of Theorem 3.2 for the combinatory filter combinator.
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


theorem valNat_filterOp : valNat filterOp = filterC :=
  (theorem_3_2_surjective filterC_combinatory).choose_spec

end DomainTheory.DataTypesAsLattices
