
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.packList
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_2

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def singleGenerator (xs : List Pomega) : Pomega :=
  funOf (funOf condC (packList xs)) Gcomb

namespace singleGenerator

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app_zero (xs : List Pomega) :
    funOf (singleGenerator xs) zeroC = packList xs :=
  _root_.DomainTheory.DataTypesAsLattices.eq_3_2 (packList xs) Gcomb

theorem mem_subalgebra {A : Set Pomega} (hA : Subalgebra A)
    {xs : List Pomega} (hxs : ∀ x, x ∈ xs → x ∈ A) :
    singleGenerator xs ∈ A := by
  have hc := combinatory_mem_subalgebra hA IsCombinatory.cond
  exact hA.out.2 (hA.out.2 hc (packList.mem_subalgebra hA hxs)) hA.out.1

end singleGenerator

end DomainTheory.DataTypesAsLattices
