module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.SetLike

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem mem_graph_const_iff (n m : ℕ) :
    m ∈ graph (fun _ => e n) ↔
      ∃ t, m = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        n.testBit (Nat.unpair t).2 = true := by
  constructor
  · intro ⟨a, b, hm, hb⟩
    exact ⟨Nat.pair a b, by simp [Nat.unpair_pair, hm],
      by simp [Nat.unpair_pair, e.mem.mp hb]⟩
  · intro ⟨t, ht, hb⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, e.mem.mpr hb⟩

end DomainTheory.DataTypesAsLattices
