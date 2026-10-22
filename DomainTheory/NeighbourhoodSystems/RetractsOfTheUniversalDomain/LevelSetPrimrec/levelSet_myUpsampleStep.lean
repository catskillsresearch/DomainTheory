module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.mod_eq_sub_of_le_of_lt_two_mul

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **The key correctness lemma for `myUpsampleStep`**: it realizes `Exercise812.lean`'s
mathematical `upsample` at the `levelSet` level, one step at a time. -/
theorem levelSet_myUpsampleStep (k m : ℕ) :
    levelSet (k + 1) (myUpsampleStep k m) = levelSet k m := by
  ext n
  simp only [mem_levelSet]
  have hlt : myModPow2 m (2 ^ k) < 2 ^ (2 ^ k) := myModPow2_lt m (2 ^ k)
  have hstep : myUpsampleStep k m
      = 2 ^ (2 ^ k) * myModPow2 m (2 ^ k) + myModPow2 m (2 ^ k) := rfl
  rw [hstep, Nat.testBit_two_pow_mul_add _ hlt]
  have hmm : n % 2 ^ k = n % 2 ^ (k + 1) % 2 ^ k :=
    (Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (Nat.le_succ k))).symm
  have hjlt : n % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt n (Nat.two_pow_pos (k + 1))
  have h2 : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  by_cases hcase : n % 2 ^ (k + 1) < 2 ^ k
  · rw [ite_eq_left hcase, myModPow2_eq, Nat.testBit_mod_two_pow, decide_eq_true_iff.mpr hcase,
      Bool.true_and, hmm, Nat.mod_eq_of_lt hcase]
  · have hge : 2 ^ k ≤ n % 2 ^ (k + 1) := Nat.le_of_not_lt hcase
    have hsub : n % 2 ^ (k + 1) - 2 ^ k < 2 ^ k := by omega
    rw [ite_eq_right hcase, myModPow2_eq, Nat.testBit_mod_two_pow, decide_eq_true_iff.mpr hsub,
      Bool.true_and, hmm, mod_eq_sub_of_le_of_lt_two_mul hge (h2 ▸ hjlt)]

end DomainTheory.NeighbourhoodSystems
