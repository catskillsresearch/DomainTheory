module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Closed LAMBDA-definable elements (empty environment). -/
class LambdaDefinable (u : Pomega) : Prop where
  out : ∃ t : Term, interp t (fun _ => botElem) = u

end DomainTheory.DataTypesAsLattices
