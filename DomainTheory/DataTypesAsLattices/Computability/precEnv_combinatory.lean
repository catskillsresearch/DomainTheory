/-ai
If f and g are combinatory, then every value of their primitive-recursion environment is combinatory.

Index 3 is the recursion operator, indices 4 and 5 are f and g, indices 6 and 7 are the unpairing combinators, and index 8 is the pairing combinator. Indices 0, 1, and 2, and every index at least 9, are bottom.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.pairComb_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.botElem_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem precEnv_combinatory {f g : Pomega}
    (hf : IsCombinatory f) (hg : IsCombinatory g) :
    ∀ i, IsCombinatory (precEnv f g i)
  | 3 => primRecOpC_combinatory
  | 4 => hf
  | 5 => hg
  | 6 => unpairFstC_combinatory
  | 7 => unpairSndC_combinatory
  | 8 => pairComb_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 9 => botElem_combinatory

end DomainTheory.DataTypesAsLattices
