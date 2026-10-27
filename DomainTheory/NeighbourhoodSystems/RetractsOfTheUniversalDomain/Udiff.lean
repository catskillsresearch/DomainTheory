module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vinter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem

theorem U_union_UX_mem (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨⟨L1, hL1⟩, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨⟨L2, hL2⟩, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨L1 ++ L2, by rw [presentedIntervals.append, hL1, hL2]⟩,
    hne1.mono Set.subset_union_left, Set.union_subset hsub1 hsub2⟩

def VunionRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myLor
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem decodeQPairList_appendListCode (c1 c2 : ℕ) :
    decodeQPairList (appendListCode c1 c2) = decodeQPairList c1 ++ decodeQPairList c2 := by
  unfold decodeQPairList
  rw [appendListCode_eq, List.map_append]

def lowXor (x y : ℕ) : ℕ := (x % 2 + y % 2) % 2

def xorStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2))

def myXor (a b : ℕ) : ℕ :=
  (xorStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

def myAndNot (a b : ℕ) : ℕ := myXor a (myLand a b)

def VdiffRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myAndNot
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem myXor_eq_xor (a b : ℕ) : myXor a b = a ^^^ b := by
  have xor_low_rec : ∀ x y : ℕ, x ^^^ y = 2 * (x / 2 ^^^ y / 2) + lowXor x y := by
    intro x y
    have hdiv : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [← Nat.testBit_add_one, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_add_one,
        Nat.testBit_add_one]
    have hmod : lowXor x y = (x ^^^ y) % 2 := by
      unfold lowXor
      rw [Nat.xor_mod_two_eq]
      exact (Nat.add_mod x y 2).symm
    conv_lhs => rw [← Nat.div_add_mod (x ^^^ y) 2]
    rw [hdiv, hmod]
  have xorStep_iter_spec : ∀ k,
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
          2 ^ k * (a / 2 ^ k ^^^ b / 2 ^ k) = a ^^^ b := by
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
      have p11 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
          = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
        unfold xorStep; rw [unpair_pair_fst, unpair_pair_fst]
      have p12 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
          = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
        unfold xorStep; rw [unpair_pair_fst, unpair_pair_snd]
      have p21 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
          = 2 * (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
        unfold xorStep; rw [unpair_pair_snd, unpair_pair_fst]
      have p22 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
          = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
            + (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
              * lowXor (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                  (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
        unfold xorStep; rw [unpair_pair_snd, unpair_pair_snd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [p21, hW, ← pow_succ']
      · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, xor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
        ring
  unfold myXor
  obtain ⟨_, _, _, hAcc⟩ := xorStep_iter_spec (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

theorem myAndNot_eq (a b : ℕ) : myAndNot a b = a ^^^ (a &&& b) := by
  unfold myAndNot; rw [myXor_eq_xor, myLand_eq_land]

def B812e : ComputableBisection VComputablePresentation where
  left := splitVLeft
  right := splitVRight
  left_primrec := primrec_splitVLeft
  right_primrec := primrec_splitVRight
  disjoint := splitV_disjoint
  union := splitV_union
  left_congr := fun _ _ h => splitVLeft_congr h
  right_congr := fun _ _ h => splitVRight_congr h

def Udiff (n m : ℕ) : ℕ := diffCode (canonCode n) (canonCode m)

theorem U_diff_iff_nonempty (n m : ℕ) :
    (∃ k, UX k = UX n \ UX m) ↔ (UX n \ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact (U_mem_UX k).2.1
  · intro hne
    rcases U.diff_mem (U_mem_UX n) (U_mem_UX m) with hempty | hmem
    · exact absurd hempty hne.ne_empty
    · exact U_surj_UX hmem

namespace Udiff
open Domain.Recursive NeighborhoodSystem

theorem eq_diff (n m : ℕ) :
    presentedIntervals (decodeQPairList (Udiff n m)) = UX n \ UX m := by
  unfold Udiff
  exact presentedIntervals_decodeQPairList_diffCode (canonCode n) (canonCode m)

theorem primrec : Nat.Primrec (fun t : ℕ => Udiff t.unpair.1 t.unpair.2) := by
  unfold Udiff
  exact (primrec_diffCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end Udiff
open Domain.Recursive NeighborhoodSystem

namespace Udiff
open Domain.Recursive NeighborhoodSystem

theorem spec {n m : ℕ} (h : ∃ k, UX k = UX n \ UX m) : UX (Udiff n m) = UX n \ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Udiff n m))) := by
    rw [Udiff.eq_diff]
    obtain ⟨k, hk⟩ := h
    rw [← hk]; exact U_mem_UX k
  show presentedIntervals (decodeQPairList (canonCode (Udiff n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Udiff.eq_diff]

end Udiff
open Domain.Recursive NeighborhoodSystem

def U_isComputableDiff : IsComputableDiff UComputablePresentation where
  diffIdx := Udiff
  diffIdx_primrec := Udiff.primrec
  diffIdx_spec := Udiff.spec
  diff_computable := by
    unfold RecDecidable₂
    refine RecDecidable.of_iff (fun t => ?_)
      (recDecidable_presentedIntervals_nonempty.comp Udiff.primrec)
    show (∃ k, UX k = UX t.unpair.1 \ UX t.unpair.2) ↔ _
    rw [U_diff_iff_nonempty, ← Udiff.eq_diff]

end DomainTheory.NeighbourhoodSystems
