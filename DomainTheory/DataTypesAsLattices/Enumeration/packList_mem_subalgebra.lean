module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_mem_subalgebra

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































theorem packList_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A) :
    ∀ {xs : List Pomega}, (∀ x, x ∈ xs → x ∈ A) → packList xs ∈ A
  | [], _ => combinatory_mem_subalgebra hA bot_combinatory
  | x :: xs, hxs =>
      seq2_mem_subalgebra hA (hxs x (by simp))
        (packList_mem_subalgebra hA fun y hy => hxs y (by simp [hy]))

end DomainTheory.DataTypesAsLattices
