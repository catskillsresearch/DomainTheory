module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.packList_mem_subalgebra

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem singleGenerator_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {xs : List Pomega} (hxs : ∀ x, x ∈ xs → x ∈ A) :
    singleGenerator xs ∈ A := by
  have hc := combinatory_mem_subalgebra hA IsCombinatory.cond
  exact hA.2 (hA.2 hc (packList_mem_subalgebra hA hxs)) hA.1

end DomainTheory.DataTypesAsLattices
