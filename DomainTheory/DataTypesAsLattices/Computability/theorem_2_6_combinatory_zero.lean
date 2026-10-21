/-ai
The zero combinator zeroC is lambda-definable, matching one of the constants among the closed lambda terms of Theorem 2.4.

It is the interpretation of the closed term Term.zero.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- Combinatory elements are generated from the six constants, matching
the LAMBDA-definable closed terms of Theorem 2.4. -/
theorem theorem_2_6_combinatory_zero : IsLambdaDefinable zeroC :=
  ⟨Term.zero, rfl⟩

end DomainTheory.DataTypesAsLattices
