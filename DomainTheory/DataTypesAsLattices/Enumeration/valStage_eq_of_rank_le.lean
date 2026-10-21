/-ai
If the rank of n is at most a stage s, then applying the s-fold iterate of the enumerator step from bottom to the numeral of n equals the numerical value of n.

The proof recurses on n. A zero argument at stage zero, and a successor argument at stage zero, contradict the rank hypothesis. A zero argument at a successor stage equals the G combinator on both sides, by the zero clauses of the step and of the evaluator. A successor argument at a successor stage reduces, by the two successor clauses, to the two unpairing components at the preceding stage. Their ranks are at most that stage by the definition of rank, so the inductive hypothesis applies. Each recursive call is at an unpairing component, which is strictly smaller than the paired code.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app_succ

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



































theorem valStage_eq_of_rank_le : ∀ n s, valRank n ≤ s →
    funOf (iterateBot valStep s) (ofNat n) = valNat n
  | 0, 0, h => by simp [valRank] at h
  | 0, s + 1, _ => by
      rw [iterateBot, valStep_app_zero, valNat_zero]
  | p + 1, 0, h => by simp [valRank] at h
  | p + 1, s + 1, h => by
      rw [iterateBot, valStep_app_succ, valNat_succ]
      have hleft : valRank (unpair p).1 ≤ s := by
        simp only [valRank] at h
        omega
      have hright : valRank (unpair p).2 ≤ s := by
        simp only [valRank] at h
        omega
      rw [valStage_eq_of_rank_le (unpair p).1 s hleft,
        valStage_eq_of_rank_le (unpair p).2 s hright]
termination_by n => n
decreasing_by
  · exact (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)
  · exact (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)

end DomainTheory.DataTypesAsLattices
