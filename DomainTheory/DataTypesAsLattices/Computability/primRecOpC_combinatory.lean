/-ai
The curried primitive-recursion operator primRecOpC is combinatory.

Unfold primRecOpC and apply the completeness law theorem_2_4_complete. The interpreted term is combinatory by ofComb_combinatory, because every value of the environment primRecOpEnv is combinatory.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpEnv_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

































theorem primRecOpC_combinatory : IsCombinatory primRecOpC := by
  rw [primRecOpC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ primRecOpEnv_combinatory

end DomainTheory.DataTypesAsLattices
