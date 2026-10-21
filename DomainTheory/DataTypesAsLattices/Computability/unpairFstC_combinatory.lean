/-ai
The first unpairing projection unpairFstC is combinatory.

Unfold unpairFstC and apply theorem_2_4_complete. The interpreted term is combinatory by ofComb_combinatory, because every value of unpairEnv is combinatory.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem unpairFstC_combinatory : IsCombinatory unpairFstC := by
  rw [unpairFstC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ unpairEnv_combinatory

end DomainTheory.DataTypesAsLattices
