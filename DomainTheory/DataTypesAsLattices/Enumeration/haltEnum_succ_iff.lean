module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code















theorem haltEnum_succ_iff (m : ℕ) :
    (∃ t, haltEnum t = m + 1) ↔ (eval (Denumerable.ofNat Code m) 0).Dom := by
  constructor
  · intro ⟨t, ht⟩
    have hs : (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome = true := by
      by_contra h
      have : haltEnum t = 0 := by
        simp [haltEnum, Bool.eq_false_of_not_eq_true h]
      omega
    have : haltEnum t = t.unpair.1 + 1 := by simp [haltEnum, hs]
    have hm : t.unpair.1 = m := by omega
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hs
    exact Part.dom_iff_mem.mpr ⟨val, evaln_sound (by simpa [hm] using hval)⟩
  · intro hdom
    obtain ⟨val, hval⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨s, hs⟩ := evaln_complete.mp hval
    refine ⟨Nat.pair m s, ?_⟩
    simp [haltEnum, Nat.unpair_pair, Option.isSome_of_mem hs]

end DomainTheory.DataTypesAsLattices
