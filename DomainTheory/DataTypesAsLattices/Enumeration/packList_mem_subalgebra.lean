/-ai
If A is a subalgebra and every component of a list lies in A, then the packing of the list lies in A.

The empty packing is the bottom element, which is combinatory and therefore lies in A. The packing of a cons cell is the binary sequence of the head with the packed tail. The head lies in A by hypothesis, the packed tail lies in A by the inductive hypothesis, and binary sequencing preserves membership in a subalgebra.
ai-/
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
