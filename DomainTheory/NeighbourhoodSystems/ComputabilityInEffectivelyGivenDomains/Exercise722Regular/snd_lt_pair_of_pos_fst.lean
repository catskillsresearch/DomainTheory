/-ai
If a is strictly positive, then b is strictly smaller than the pairing of a with b.

Rewrite by the definition of pairing and split on its conditional. In the first branch, transitivity gives that b is positive, so b is at most b times b by rewriting b as 1 times b and multiplying on the right; then b times b is strictly smaller than b times b plus a, and omega closes the goal. In the other branch, a is at most a times a plus a, so that sum is positive, and omega closes the goal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

theorem snd_lt_pair_of_pos_fst {a b : ℕ} (ha : 0 < a) : b < Nat.pair a b := by
  rw [Nat.pair]
  split_ifs with h
  · have hb : 0 < b := Nat.lt_trans ha h
    have hbb : b ≤ b * b := by
      calc
        b = 1 * b := (Nat.one_mul b).symm
        _ ≤ b * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hb)
    have : b * b < b * b + a := Nat.lt_add_of_pos_right ha
    omega
  · have : 0 < a * a + a := by
      have : a ≤ a * a + a := Nat.le_add_left _ _
      omega
    omega

end Exercise722

end DomainTheory.NeighbourhoodSystems
