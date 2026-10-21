/-ai
Every value of the unpairing environment unpairEnv is combinatory.

At indices 1, 2, 3, and 4 this is the combinatory status of sqrtC, subC, mulC, and leC. At index 0, and at every index of the form n + 5, it is botElem_combinatory.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.subC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.mulC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.leC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.botElem_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem unpairEnv_combinatory : ∀ i, IsCombinatory (unpairEnv i)
  | 1 => sqrtC_combinatory
  | 2 => subC_combinatory
  | 3 => mulC_combinatory
  | 4 => leC_combinatory
  | 0 => botElem_combinatory
  | _ + 5 => botElem_combinatory

end DomainTheory.DataTypesAsLattices
