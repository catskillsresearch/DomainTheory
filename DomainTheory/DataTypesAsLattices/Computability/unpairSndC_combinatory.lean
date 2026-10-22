module

public import Mathlib.Computability.RE
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


theorem unpairSndC_combinatory : IsCombinatory unpairSndC := by
  rw [unpairSndC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ unpairEnv_combinatory

end DomainTheory.DataTypesAsLattices
