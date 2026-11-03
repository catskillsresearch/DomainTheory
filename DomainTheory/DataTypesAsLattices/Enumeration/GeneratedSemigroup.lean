module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

inductive GeneratedSemigroup : Pomega → Prop
  | R : GeneratedSemigroup Rcomb
  | L : GeneratedSemigroup Lcomb
  | Gbar : GeneratedSemigroup Gbar
  | comp {u v} : GeneratedSemigroup u → GeneratedSemigroup v →
      GeneratedSemigroup (enumComp u v)

end DomainTheory.DataTypesAsLattices
