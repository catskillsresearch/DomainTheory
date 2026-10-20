module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem mem_graph_const_iff (n m : ℕ) :
    m ∈ graph (fun _ => e n) ↔
      ∃ t, m = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        n.testBit (Nat.unpair t).2 = true := by
  constructor
  · intro ⟨a, b, hm, hb⟩
    exact ⟨Nat.pair a b, by simp [Nat.unpair_pair, hm],
      by simp [Nat.unpair_pair, mem_e.mp hb]⟩
  · intro ⟨t, ht, hb⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, mem_e.mpr hb⟩

end DomainTheory.DataTypesAsLattices
