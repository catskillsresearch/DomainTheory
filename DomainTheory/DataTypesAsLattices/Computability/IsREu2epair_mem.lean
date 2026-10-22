module

public import Mathlib.Computability.RE
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
  hu.out.comp primrec_pair.to_comp

end DomainTheory.DataTypesAsLattices
