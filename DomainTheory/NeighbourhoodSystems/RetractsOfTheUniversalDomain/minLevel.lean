module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vinter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace myTestBit
open Domain.Recursive NeighborhoodSystem

theorem le_one (m ℓ : ℕ) : myTestBit m ℓ ≤ 1 := by
  unfold myTestBit
  rcases Nat.mod_two_eq_zero_or_one (myDivPow2 m ℓ) with h | h <;> omega

end myTestBit
open Domain.Recursive

def isPeriodicMask (k j m : ℕ) : ℕ :=
  isZero ((myUpsample j k (myModPow2 m (2 ^ j)) - myModPow2 m (2 ^ k)) +
    (myModPow2 m (2 ^ k) - myUpsample j k (myModPow2 m (2 ^ j))))

def minLevel (k m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (isPeriodicMask k i m) i (i + 1)) ih) (k + 1)

def minLevelFold (k m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (isPeriodicMask k i m) i (i + 1)) ih) N

def minMask (k m : ℕ) : ℕ := myModPow2 m (2 ^ minLevel k m)

theorem isPeriodicMask_le_one (k j m : ℕ) : isPeriodicMask k j m ≤ 1 := isZero_le_one _

theorem isPeriodicMask_eq_one_iff (k j m : ℕ) :
    isPeriodicMask k j m = 1 ↔ myUpsample j k (myModPow2 m (2 ^ j)) = myModPow2 m (2 ^ k) := by
  unfold isPeriodicMask
  rw [isZero_eq_one_iff]
  omega

theorem isPeriodicMask_iff {k j m : ℕ} (hj : j ≤ k) :
    isPeriodicMask k j m = 1 ↔ levelSet k m = levelSet j m := by
  rw [isPeriodicMask_eq_one_iff]
  constructor
  · intro h
    have h1 :
        levelSet k (myUpsample j k (myModPow2 m (2 ^ j))) = levelSet k (myModPow2 m (2 ^ k)) := by
      rw [h]
    rw [levelSet.myUpsample hj, levelSet.myModPow2, levelSet.myModPow2] at h1
    exact h1.symm
  · intro h
    apply levelSet.inj_of_lt (myUpsample_lt _ _ _) (myModPow2.lt _ _)
    rw [levelSet.myUpsample hj, levelSet.myModPow2, levelSet.myModPow2]
    exact h.symm

theorem isPeriodicMask_self (k m : ℕ) : isPeriodicMask k k m = 1 := by
  rw [isPeriodicMask_eq_one_iff]
  unfold myUpsample
  simp only [Nat.sub_self, Function.iterate_zero, id_eq, unpair_pair_snd]
  rw [myModPow2.eq, myModPow2.eq, Nat.mod_eq_of_lt (Nat.mod_lt m (Nat.two_pow_pos (2 ^ k)))]

theorem minLevel_eq_fold (k m : ℕ) : minLevel k m = minLevelFold k m (k + 1) := rfl

private theorem minLevelFold_succ (k m N : ℕ) :
    minLevelFold k m (N + 1) =
      selectFn (isZero (N - minLevelFold k m N))
        (selectFn (isPeriodicMask k N m) N (N + 1)) (minLevelFold k m N) := rfl

private theorem minLevelFold_spec (k m N : ℕ) :
    (minLevelFold k m N < N ∧ isPeriodicMask k (minLevelFold k m N) m = 1 ∧
        ∀ j < minLevelFold k m N, isPeriodicMask k j m ≠ 1) ∨
      (minLevelFold k m N = N ∧ ∀ j < N, isPeriodicMask k j m ≠ 1) := by
  induction N with
  | zero => exact Or.inr ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ i ih =>
    rw [minLevelFold_succ]
    rcases ih with ⟨hlt, htrue, hmin⟩ | ⟨heq, hall⟩
    · have hne : i - minLevelFold k m i ≠ 0 := by omega
      have hz : isZero (i - minLevelFold k m i) = 0 := by
        have hle := isZero_le_one (i - minLevelFold k m i)
        rcases (show isZero (i - minLevelFold k m i) = 0 ∨
            isZero (i - minLevelFold k m i) = 1 by omega) with h | h
        · exact h
        · exact absurd ((isZero_eq_one_iff _).mp h) hne
      rw [hz, selectFn_zero]
      exact Or.inl ⟨by omega, htrue, hmin⟩
    · have hz : isZero (i - minLevelFold k m i) = 1 :=
        (isZero_eq_one_iff _).mpr (by omega)
      rw [hz, selectFn_one]
      have hle : isPeriodicMask k i m ≤ 1 := isPeriodicMask_le_one k i m
      rcases (show isPeriodicMask k i m = 0 ∨ isPeriodicMask k i m = 1 by omega) with hbit | hbit
      · rw [hbit, selectFn_zero]
        refine Or.inr ⟨by omega, fun j hj => ?_⟩
        rcases (show j < i ∨ j = i by omega) with hlt' | heq'
        · exact hall j hlt'
        · subst heq'; omega
      · rw [hbit, selectFn_one]
        exact Or.inl ⟨by omega, hbit, fun j hj => hall j (by omega)⟩

theorem minLevel_le (k m : ℕ) : minLevel k m ≤ k := by
  rw [minLevel_eq_fold]
  rcases minLevelFold_spec k m (k + 1) with ⟨h, -, -⟩ | ⟨heq, hall⟩
  · omega
  · exact absurd (isPeriodicMask_self k m) (hall k (by omega))

theorem minLevel_isPeriodicMask (k m : ℕ) : isPeriodicMask k (minLevel k m) m = 1 := by
  rw [minLevel_eq_fold]
  rcases minLevelFold_spec k m (k + 1) with ⟨-, htrue, -⟩ | ⟨heq, hall⟩
  · exact htrue
  · exact absurd (isPeriodicMask_self k m) (hall k (by omega))

theorem minLevel_min {k m j : ℕ} (hj : j < minLevel k m) : isPeriodicMask k j m ≠ 1 := by
  revert hj
  rw [minLevel_eq_fold]
  intro hj
  rcases minLevelFold_spec k m (k + 1) with ⟨-, -, hmin⟩ | ⟨heq, hall⟩
  · exact hmin j hj
  · exact hall j (heq ▸ hj)

theorem levelSet_minLevel (k m : ℕ) : levelSet (minLevel k m) (minMask k m) = levelSet k m := by
  have h := (isPeriodicMask_iff (minLevel_le k m)).1 (minLevel_isPeriodicMask k m)
  show levelSet (minLevel k m) (myModPow2 m (2 ^ minLevel k m)) = levelSet k m
  rw [levelSet.myModPow2, h]

theorem levelSet_presentable_imp_self {k j m m' : ℕ} (hj : j ≤ k)
    (h : levelSet j m' = levelSet k m) : levelSet k m = levelSet j m := by
  have hraw : ∀ i, i < 2 ^ k → m.testBit i = m.testBit (i % 2 ^ j) := by
    intro i hi
    have hik : i % 2 ^ j < 2 ^ k :=
      lt_of_lt_of_le (Nat.mod_lt i (Nat.two_pow_pos j))
        (Nat.pow_le_pow_right (by norm_num) hj)
    have e1 : m'.testBit (i % 2 ^ j) = m.testBit (i % 2 ^ k) := by
      have hiff := Set.ext_iff.mp h i
      simp only [mem_levelSet] at hiff
      cases ha : m'.testBit (i % 2 ^ j) <;> cases hb : m.testBit (i % 2 ^ k) <;>
        simp_all
    have e2 : m'.testBit ((i % 2 ^ j) % 2 ^ j) = m.testBit ((i % 2 ^ j) % 2 ^ k) := by
      have hiff := Set.ext_iff.mp h (i % 2 ^ j)
      simp only [mem_levelSet] at hiff
      cases ha : m'.testBit ((i % 2 ^ j) % 2 ^ j) <;> cases hb : m.testBit ((i % 2 ^ j) % 2 ^ k) <;>
        simp_all
    rw [Nat.mod_eq_of_lt hi] at e1
    rw [Nat.mod_eq_of_lt (Nat.mod_lt i (Nat.two_pow_pos j)), Nat.mod_eq_of_lt hik] at e2
    rw [← e1, ← e2]
  ext n
  simp only [mem_levelSet]
  have := hraw (n % 2 ^ k) (Nat.mod_lt n (Nat.two_pow_pos k))
  rw [this, Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hj)]

theorem isPeriodicMask_of_presentable {k j m : ℕ} (hj : j ≤ k) {m' : ℕ}
    (h : levelSet j m' = levelSet k m) : isPeriodicMask k j m = 1 :=
  (isPeriodicMask_iff hj).2 (levelSet_presentable_imp_self hj h)

theorem minLevel_eq {k₁ m₁ k₂ m₂ : ℕ} (h : levelSet k₁ m₁ = levelSet k₂ m₂) :
    minLevel k₁ m₁ = minLevel k₂ m₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hpres : levelSet (minLevel k₁ m₁) (minMask k₁ m₁) = levelSet k₂ m₂ := by
      rw [levelSet_minLevel]; exact h
    have hj : minLevel k₁ m₁ ≤ k₂ := le_trans (le_of_lt hlt) (minLevel_le k₂ m₂)
    exact minLevel_min (k := k₂) (m := m₂) (j := minLevel k₁ m₁) hlt
      (isPeriodicMask_of_presentable hj hpres)
  · have hpres : levelSet (minLevel k₂ m₂) (minMask k₂ m₂) = levelSet k₁ m₁ := by
      rw [levelSet_minLevel]; exact h.symm
    have hj : minLevel k₂ m₂ ≤ k₁ := le_trans (le_of_lt hlt) (minLevel_le k₁ m₁)
    exact minLevel_min (k := k₁) (m := m₁) (j := minLevel k₂ m₂) hlt
      (isPeriodicMask_of_presentable hj hpres)

theorem minMask_eq {k₁ m₁ k₂ m₂ : ℕ} (h : levelSet k₁ m₁ = levelSet k₂ m₂) :
    minMask k₁ m₁ = minMask k₂ m₂ := by
  have hlvl := minLevel_eq h
  have hsets : levelSet (minLevel k₁ m₁) (minMask k₁ m₁) = levelSet (minLevel k₁ m₁) (minMask k₂ m₂) := by
    rw [levelSet_minLevel, hlvl, levelSet_minLevel, h]
  have hb1 : minMask k₁ m₁ < 2 ^ (2 ^ minLevel k₁ m₁) := myModPow2.lt _ _
  have hb2 : minMask k₂ m₂ < 2 ^ (2 ^ minLevel k₁ m₁) := hlvl ▸ myModPow2.lt _ _
  exact levelSet.inj_of_lt hb1 hb2 hsets

theorem minLevel_unique {k₁ m₁ k₂ m₂ : ℕ} (h : levelSet k₁ m₁ = levelSet k₂ m₂) :
    minLevel k₁ m₁ = minLevel k₂ m₂ ∧ minMask k₁ m₁ = minMask k₂ m₂ :=
  ⟨minLevel_eq h, minMask_eq h⟩

theorem primrec_isPeriodicMask :
    Nat.Primrec (fun t => isPeriodicMask t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hj : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hmodj : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2.unpair.2 (2 ^ t.unpair.2.unpair.1)) :=
    (primrec.myModPow2.comp (hm.pair (primrec_two_pow hj))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hmodk : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2.unpair.2 (2 ^ t.unpair.1)) :=
    (primrec.myModPow2.comp (hm.pair (primrec_two_pow hk))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hups : Nat.Primrec (fun t : ℕ =>
      myUpsample t.unpair.2.unpair.1 t.unpair.1 (myModPow2 t.unpair.2.unpair.2
        (2 ^ t.unpair.2.unpair.1))) :=
    (primrec.myUpsample.comp (hj.pair (hk.pair hmodj))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_isZero.comp (primrec_add₂ (primrec_sub₂ hups hmodk)
    (primrec_sub₂ hmodk hups))).of_eq fun t => rfl

theorem primrec_minLevel : Nat.Primrec (fun t => minLevel t.unpair.1 t.unpair.2) := by

  have hk : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hm : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hsub : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 - w.unpair.2.unpair.2) :=
    primrec_sub₂ hi hih
  have hpm : Nat.Primrec (fun w : ℕ => isPeriodicMask w.unpair.1.unpair.1 w.unpair.2.unpair.1
      w.unpair.1.unpair.2) :=
    (primrec_isPeriodicMask.comp (hk.pair (hi.pair hm))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hsucc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 1) := Nat.Primrec.succ.comp hi
  have hGfn : Nat.Primrec (fun w =>
      selectFn (isZero (w.unpair.2.unpair.1 - w.unpair.2.unpair.2))
        (selectFn (isPeriodicMask w.unpair.1.unpair.1 w.unpair.2.unpair.1 w.unpair.1.unpair.2)
          w.unpair.2.unpair.1 (w.unpair.2.unpair.1 + 1))
        w.unpair.2.unpair.2) :=
    primrec_selectFn (primrec_isZero.comp hsub) (primrec_selectFn hpm hi hsucc) hih
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair t (t.unpair.1 + 1)) :=
    Nat.Primrec.id.pair (Nat.Primrec.succ.comp Nat.Primrec.left)
  refine (hprec.comp hpack).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

theorem primrec_minMask : Nat.Primrec (fun t => minMask t.unpair.1 t.unpair.2) := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hlvl : Nat.Primrec (fun t : ℕ => minLevel t.unpair.1 t.unpair.2) := primrec_minLevel
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ minLevel t.unpair.1 t.unpair.2) :=
    primrec_two_pow hlvl
  exact (primrec.myModPow2.comp (hm.pair hpow)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd, minMask]

end DomainTheory.NeighbourhoodSystems
