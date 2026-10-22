/-ai
A set of natural numbers is closed lambda-definable when some term interprets to it in the environment that sends every variable to the empty set.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Closed LAMBDA-definable elements (empty environment). -/
class LambdaDefinable (u : Pomega) : Prop where
  out : ∃ t : Term, interp t (fun _ => botElem) = u

end DomainTheory.DataTypesAsLattices
