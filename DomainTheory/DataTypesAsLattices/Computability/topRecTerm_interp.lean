/-ai
The interpretation of topRecTerm in the constantly bottom environment equals the graph of topRec.

Congruence reduces the claim to agreement of the underlying functions. Extensionality and simplification of topRec, the interpretation, the environment update, and equation eq_2_15 give that identity.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem topRecTerm_interp :
    interp topRecTerm (fun _ => botElem) = graph topRec := by
  apply congrArg graph
  funext v
  simp [topRec, interp, envSet, Function.update, eq_2_15]

end DomainTheory.DataTypesAsLattices
