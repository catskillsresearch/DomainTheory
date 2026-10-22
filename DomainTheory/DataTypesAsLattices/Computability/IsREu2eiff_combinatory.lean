/-ai
A set of natural numbers is recursively enumerable if and only if it is combinatory.

One direction is the theorem that every recursively enumerable set is combinatory, and the other is the theorem that every combinatory set is recursively enumerable.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isRE
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ecombinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem IsRE.iff_combinatory {u : Pomega} : IsRE u ↔ IsCombinatory u :=
  ⟨IsRE.combinatory, combinatory_isRE⟩

end DomainTheory.DataTypesAsLattices
