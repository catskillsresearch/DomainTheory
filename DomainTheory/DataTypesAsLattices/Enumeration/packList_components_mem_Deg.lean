/-ai
If the packing of a list lies in the degree of an element a, then every component of the list lies in that degree.

The empty list contributes no component. For a cons cell, the numerals 0 and 1 are combinatory, so they lie in the degree. The subalgebra operation of the degree, applied to the packing and to 0, recovers the head by the zero law for binary sequencing, and applied to the packing and to 1 it recovers the packed tail by the one law. The head therefore lies in the degree, and the inductive hypothesis places every remaining component in the degree.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_Deg

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem packList_components_mem_Deg {a : Pomega} :
    ∀ {xs : List Pomega}, packList xs ∈ Deg a →
      ∀ x, x ∈ xs → x ∈ Deg a
  | [], _hp, x, hx => by simp at hx
  | y :: ys, hp, x, hx => by
      have h0 := combinatory_mem_Deg a (ofNat_combinatory 0)
      have h1 := combinatory_mem_Deg a (ofNat_combinatory 1)
      have hy : y ∈ Deg a := by
        have := (Deg_isSubalgebra a).2 hp h0
        simpa [packList, seq2_app_zero] using this
      have htail : packList ys ∈ Deg a := by
        have := (Deg_isSubalgebra a).2 hp h1
        simpa [packList, seq2_app_one] using this
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact packList_components_mem_Deg htail x hx

end DomainTheory.DataTypesAsLattices
