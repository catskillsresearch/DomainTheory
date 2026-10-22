module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem botElem_combinatory : IsCombinatory botElem := by
  have h : predC ⬝ zeroC = botElem := by
    rw [predC_app]
    simpa [zeroC] using eq_2_6
  exact h ▸ .app .pred .zero

end DomainTheory.DataTypesAsLattices
