module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_Deg
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_mem_subalgebra

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def packList : List Pomega → Pomega
  | [] => botElem
  | x :: xs => seq2 x (packList xs)

namespace packList

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem components_mem_Deg {a : Pomega} :
    ∀ {xs : List Pomega}, packList xs ∈ Deg a →
      ∀ x, x ∈ xs → x ∈ Deg a
  | [], _hp, x, hx => by simp at hx
  | y :: ys, hp, x, hx => by
      have h0 := combinatory_mem_Deg a (ofNat.combinatory 0)
      have h1 := combinatory_mem_Deg a (ofNat.combinatory 1)
      have hy : y ∈ Deg a := by
        have := (Deg.isSubalgebra a).out.2 hp h0
        simpa [packList, seq2.zero] using this
      have htail : packList ys ∈ Deg a := by
        have := (Deg.isSubalgebra a).out.2 hp h1
        simpa [packList, seq2.one] using this
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact components_mem_Deg htail x hx

theorem cons_zero (x : Pomega) (xs : List Pomega) :
    funOf (packList (x :: xs)) (ofNat 0) = x :=
  seq2.zero x (packList xs)

theorem mem_subalgebra {A : Set Pomega} (hA : Subalgebra A) :
    ∀ {xs : List Pomega}, (∀ x, x ∈ xs → x ∈ A) → packList xs ∈ A
  | [], _ => combinatory_mem_subalgebra hA bot_combinatory
  | x :: xs, hxs =>
      seq2_mem_subalgebra hA (hxs x (by simp))
        (mem_subalgebra hA fun y hy => hxs y (by simp [hy]))

end packList

end DomainTheory.DataTypesAsLattices
