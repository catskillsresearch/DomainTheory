/-ai
The numerical evaluator sends the bottom code to the bottom element.

The equality is the specification of the witness chosen by the surjectivity clause of Theorem 3.2 for the combinatory bottom element.
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































































theorem valNat_botCode : valNat botCode = botElem :=
  (theorem_3_2_surjective bot_combinatory).choose_spec

end DomainTheory.DataTypesAsLattices
