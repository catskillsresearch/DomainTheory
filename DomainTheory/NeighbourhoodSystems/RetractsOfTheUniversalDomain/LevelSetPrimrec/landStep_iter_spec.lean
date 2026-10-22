module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.landStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.land_low_rec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Invariant of the bitwise-AND iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k &&& b/2^k) = a &&& b`. -/
theorem landStep_iter_spec (a b : ℕ) : ∀ k,
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k &&& b / 2 ^ k) = a &&& b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have p11 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold landStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold landStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold landStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowAnd (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold landStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, land_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

end DomainTheory.NeighbourhoodSystems
