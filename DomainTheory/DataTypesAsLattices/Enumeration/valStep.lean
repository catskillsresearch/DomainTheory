/-ai
Scott 1976, (3.7). One step of the enumerator sends a value v to the graph of the map which returns the McCarthy conditional of the code, with zero branch the G combinator and positive branch the minimal extension of the application selected by v at that code. The positive branch is that minimal extension, which agrees extensionally with Scott's existential clause and displays the continuity of the step.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.valStepValue

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.7).** One step of the enumerator.  The positive
branch is written as `minExtend`; this is extensionally Scott's existential
clause and exposes its continuity. -/
def valStep (v : Pomega) : Pomega :=
  graph (fun k => condSet k Gcomb (minExtend (valStepValue v) k))

end DomainTheory.DataTypesAsLattices
