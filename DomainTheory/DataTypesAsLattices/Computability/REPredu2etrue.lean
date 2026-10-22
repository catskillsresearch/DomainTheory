/-ai
The constantly true predicate on a primcodable type is recursively enumerable.

Unfold the definition and take the constant partial function with value the unit. Extensionality and the characterization of assertion show that it asserts truth.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem REPred.true {α} [Primcodable α] : REPred fun _ : α => True := by
  unfold REPred
  refine (Decidable.Partrec.const' (Part.some ())).of_eq fun _ => ?_
  ext
  simp [Part.assert]

end DomainTheory.DataTypesAsLattices
