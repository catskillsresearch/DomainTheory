/-ai
The numerical evaluator sends the intersection code to the intersection combinator.

The equality is the specification of the witness chosen by the surjectivity clause of Theorem 3.2 for the combinatory intersection combinator.
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























































theorem valNat_interCode : valNat interCode = interC :=
  (theorem_3_2_surjective interC_combinatory).choose_spec

end DomainTheory.DataTypesAsLattices
