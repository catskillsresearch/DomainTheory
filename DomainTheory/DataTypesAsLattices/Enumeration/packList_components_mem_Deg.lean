module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
