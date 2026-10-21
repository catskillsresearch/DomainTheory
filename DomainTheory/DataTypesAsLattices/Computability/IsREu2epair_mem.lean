/-ai
If a set is recursively enumerable, then the predicate that the pair of two numbers lies in the set is recursively enumerable.

It is the recursively enumerable membership predicate composed with the primitive recursive pairing function.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.pair_mem {u : Pomega} (hu : IsRE u) :
    REPred fun q : ℕ × ℕ => pair q.1 q.2 ∈ u :=
  hu.comp primrec_pair.to_comp

end DomainTheory.DataTypesAsLattices
