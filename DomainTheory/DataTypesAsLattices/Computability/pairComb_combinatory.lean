/-ai
The pairing combinator is combinatory.

Rewrite by the completeness half of Theorem 2.4, and apply the combinatory interpretation of the pairing term in the arithmetic environment.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem pairComb_combinatory : IsCombinatory pairComb := by
  rw [pairComb, theorem_2_4_complete]
  exact ofComb_combinatory _ _ arithEnv_combinatory

end DomainTheory.DataTypesAsLattices
