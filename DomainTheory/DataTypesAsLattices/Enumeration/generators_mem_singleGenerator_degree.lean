module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6_finite
public import DomainTheory.DataTypesAsLattices.Enumeration.packList_components_mem_Deg

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem generators_mem_singleGenerator_degree (xs : List Pomega) :
    ∀ x, x ∈ xs → x ∈ Deg (singleGenerator xs) :=
  packList_components_mem_Deg (theorem_3_6_finite xs).1

end DomainTheory.DataTypesAsLattices
