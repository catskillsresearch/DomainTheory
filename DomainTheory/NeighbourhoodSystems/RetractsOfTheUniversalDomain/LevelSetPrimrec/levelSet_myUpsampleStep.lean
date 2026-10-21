/-ai
One upsampling step from level k to level k + 1 presents the same set as the original
mask.

By extensionality, the truncated mask is strictly below two to the power two to the k,
and the step equals that power times the truncation plus the truncation, by reflexivity.
The test bit of this sum splits into the low and high copies. The remainder of the point
by two to the k equals the remainder by two to the k of its remainder by two to the k +
1, and the latter remainder is strictly below two to the k + 1, which equals twice two
to the k. If that remainder lies below two to the k, the low branch, the remainder form
of the bit test, and the remainder equaling itself give the original bit. Otherwise the
remainder is at least two to the k and the difference is strictly below two to the k by
arithmetic, so the high branch, the remainder form of the bit test, and the
single-wraparound law for the remainder give the original bit.
ai-/
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
