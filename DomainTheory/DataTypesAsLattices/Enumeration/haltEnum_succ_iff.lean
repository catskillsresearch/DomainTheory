/-ai
The number m + 1 lies in the range of the shifted halting enumerator if and only if evaluation of the code decoded from m on input 0 is defined.

If the enumerator returns m + 1 at an argument t, the step-bounded evaluation of the decoded first component of t on input 0, for the number of steps given by the second component, must return a value, since otherwise the enumerator would return 0. The enumerator is then one more than that first component, so the first component equals m, and soundness of step-bounded evaluation puts the returned value in the domain of evaluation. Conversely, if evaluation is defined, completeness of step-bounded evaluation supplies a stage at which the value appears, and the pair of m with that stage is a preimage under the enumerator.
ai-/
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
