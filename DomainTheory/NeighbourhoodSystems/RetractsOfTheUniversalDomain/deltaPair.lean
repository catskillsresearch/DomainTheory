module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

def encodeDeltaPair (δ : ℕ → Bool × Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => encodeDeltaPair δ n +
      ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n

namespace encodeDeltaPair

theorem lt (δ : ℕ → Bool × Bool) : ∀ n, encodeDeltaPair δ n < 4 ^ n
  | 0 => by simp [encodeDeltaPair]
  | n + 1 => by
      have ih := lt δ n
      have h4 : (4 : ℕ) ^ (n + 1) = 4 ^ n * 4 := pow_succ 4 n
      show encodeDeltaPair δ n +
        ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n < 4 ^ (n + 1)
      rcases Bool.eq_false_or_eq_true (δ n).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ n).2 with h2 | h2 <;>
        simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] <;> omega

end encodeDeltaPair

def deltaPair (k : ℕ) : ℕ → Bool × Bool :=
  fun i => (decide ((k / 4 ^ i) % 2 = 1), decide ((k / 4 ^ i / 2) % 2 = 1))

namespace deltaPair

theorem fst_eq_testBit (k i : ℕ) : (deltaPair k i).1 = k.testBit (2 * i) := by
  show decide ((k / 4 ^ i) % 2 = 1) = k.testBit (2 * i)
  rw [Nat.testBit_eq_decide_div_mod_eq, show (4 : ℕ) ^ i = 2 ^ (2 * i) by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]]

theorem snd_eq_testBit (k i : ℕ) : (deltaPair k i).2 = k.testBit (2 * i + 1) := by
  show decide ((k / 4 ^ i / 2) % 2 = 1) = k.testBit (2 * i + 1)
  rw [Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq, show (4 : ℕ) ^ i * 2 = 2 ^ (2 * i + 1)
    by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, pow_succ]]

theorem encodeDeltaPair (δ : ℕ → Bool × Bool) :
    ∀ n i, i < n → deltaPair (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · show (decide ((DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 = 1),
          decide ((DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      have key : DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i % 4 =
          DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i % 4 := by
        show (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n +
          ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ i % 4 = _
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi'
        have heq : ((if (δ (i + j + 1)).1 then 1 else 0) + (if (δ (i + j + 1)).2 then 2 else 0)) *
            4 ^ (i + j + 1) = 4 ^ i * (4 * 4 ^ j *
              ((if (δ (i + j + 1)).1 then 1 else 0) + (if (δ (i + j + 1)).2 then 2 else 0))) := by
          ring
        rw [heq, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) i)]
        rw [show 4 * 4 ^ j *
            ((if (δ (i + j + 1)).1 then 1 else 0) + (if (δ (i + j + 1)).2 then 2 else 0)) =
            4 * (4 ^ j * ((if (δ (i + j + 1)).1 then 1 else 0) +
              (if (δ (i + j + 1)).2 then 2 else 0))) by ring]
        exact Nat.add_mul_mod_self_left _ _ _
      have h1 : (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 =
          (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i) % 2 := by omega
      have h2 : (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 =
          (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i / 2) % 2 := by omega
      rw [h1, h2]
      show (decide ((DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i) % 2 = 1),
          decide ((DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i / 2) % 2 = 1)) = δ i
      exact ih i hi'
    · have hd : DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (i + 1) / 4 ^ i =
          (if (δ i).1 then 1 else 0) + (if (δ i).2 then 2 else 0) := by
        show (DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ i +
            ((if (δ i).1 then 1 else 0) + (if (δ i).2 then 2 else 0)) * 4 ^ i) / 4 ^ i = _
        rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) i),
          Nat.div_eq_of_lt (encodeDeltaPair.lt δ i), Nat.zero_add]
      show (decide ((DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (i + 1) / 4 ^ i) % 2 = 1),
          decide ((DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (i + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      rw [hd]
      rcases Bool.eq_false_or_eq_true (δ i).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ i).2 with h2 | h2 <;>
        simp [h1, h2, Prod.ext_iff]

theorem exists_ne_of_lt_of_ne {n k k' : ℕ} (hk : k < 4 ^ n) (hk' : k' < 4 ^ n)
    (hne : k ≠ k') : ∃ i < n, deltaPair k i ≠ deltaPair k' i := by
  by_contra hcon
  push Not at hcon
  exact hne (by
    apply Nat.eq_of_testBit_eq
    intro l
    rcases Nat.lt_or_ge l (2 * n) with hl | hl
    · rcases Nat.mod_two_eq_zero_or_one l with hmod | hmod
      · have hl2 : l = 2 * (l / 2) := by omega
        have hi : l / 2 < n := by omega
        have heq := congrArg Prod.fst (hcon (l / 2) hi)
        rw [fst_eq_testBit, fst_eq_testBit] at heq
        rwa [hl2]
      · have hl2 : l = 2 * (l / 2) + 1 := by omega
        have hi : l / 2 < n := by omega
        have heq := congrArg Prod.snd (hcon (l / 2) hi)
        rw [snd_eq_testBit, snd_eq_testBit] at heq
        rwa [hl2]
    · have h4n : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      have hile : (2 : ℕ) ^ (2 * n) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
      rw [Nat.testBit_lt_two_pow ((h4n ▸ hk).trans_le hile),
        Nat.testBit_lt_two_pow ((h4n ▸ hk').trans_le hile)])

end deltaPair

end DomainTheory.NeighbourhoodSystems
