/-ai
A natural number lies in the conditional combinator if and only if it is a nested pair (n₀, (n₁, (n₂, m))) such that either bit m of n₀ and bit 0 of n₂ are set, or bit m of n₁ is set and 2 ≤ n₂.

Membership unfolds as three nested pair witnesses, and the payload is rewritten by the bit criterion for the conditional on finite sets. The converse repacks the nested pair and applies that same criterion.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.condSet_e_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem mem_condC_iff (p : ℕ) :
    p ∈ condC ↔
      ∃ n0 n1 n2 m, p = pair n0 (pair n1 (pair n2 m)) ∧
        ((n0.testBit m = true ∧ n2.testBit 0 = true) ∨
          (n1.testBit m = true ∧ 2 ≤ n2)) := by
  constructor
  · intro ⟨n0, p1, hp, hp1⟩
    obtain ⟨n1, p2, hp1', hp2⟩ := hp1
    obtain ⟨n2, m, hp2', hm⟩ := hp2
    exact ⟨n0, n1, n2, m, by simp [hp, hp1', hp2'],
      (condSet_e_iff n0 n1 n2 m).mp hm⟩
  · intro ⟨n0, n1, n2, m, hp, hm⟩
    exact ⟨n0, pair n1 (pair n2 m), hp,
      ⟨n1, pair n2 m, rfl,
        ⟨n2, m, rfl, (condSet_e_iff n0 n1 n2 m).mpr hm⟩⟩⟩

end DomainTheory.DataTypesAsLattices
