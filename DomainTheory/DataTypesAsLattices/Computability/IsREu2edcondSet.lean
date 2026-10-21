/-ai
The doubly strict conditional of three recursively enumerable sets is recursively enumerable.

It is the conditional whose two branches are themselves conditionals, with the full set in the unused inner branch of each, and the conditional theorem applies to those recursively enumerable sets.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2etop
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2econdSet

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.dcondSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (dcondSet z x y) :=
  IsRE.condSet hz (IsRE.condSet hz hx IsRE.top) (IsRE.condSet hz IsRE.top hy)

end DomainTheory.DataTypesAsLattices
