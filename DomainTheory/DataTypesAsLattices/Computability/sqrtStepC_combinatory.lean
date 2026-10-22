module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.sqrtEnv_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem sqrtStepC_combinatory : IsCombinatory sqrtStepC := by
  rw [sqrtStepC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ sqrtEnv_combinatory

end DomainTheory.DataTypesAsLattices
