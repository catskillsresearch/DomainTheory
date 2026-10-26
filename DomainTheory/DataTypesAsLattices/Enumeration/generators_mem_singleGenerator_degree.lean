module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg
public import DomainTheory.DataTypesAsLattices.Enumeration.packList
public import DomainTheory.DataTypesAsLattices.Enumeration.singleGenerator
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem generators_mem_singleGenerator_degree (xs : List Pomega) :
    ∀ x, x ∈ xs → x ∈ Deg (singleGenerator xs) :=
  packList.components_mem_Deg (theorem_3_6.finite xs).1

end DomainTheory.DataTypesAsLattices
