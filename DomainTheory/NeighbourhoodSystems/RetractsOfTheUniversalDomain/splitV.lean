module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.minLevel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

def myClearBit (m ℓ : ℕ) : ℕ := m - 2 ^ ℓ

def myFirstBit (m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (myTestBit m i) i (i + 1)) ih) N

def splitVMinLevel (n : ℕ) : ℕ := minLevel (canonIdx n).unpair.1 (canonIdx n).unpair.2

def splitVMinMask (n : ℕ) : ℕ := minMask (canonIdx n).unpair.1 (canonIdx n).unpair.2

def splitVUpsampled (n : ℕ) : ℕ :=
  myUpsample (splitVMinLevel n) (splitVMinLevel n + 1) (splitVMinMask n)

def splitVBit (n : ℕ) : ℕ :=
  myFirstBit (splitVUpsampled n) (2 ^ (splitVMinLevel n + 1))

def splitVLeft (n : ℕ) : ℕ := Nat.pair (splitVMinLevel n + 1) (2 ^ splitVBit n)

def splitVRight (n : ℕ) : ℕ :=
  Nat.pair (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n))

theorem myFirstBit_succ (m i : ℕ) :
    myFirstBit m (i + 1) =
      selectFn (isZero (i - myFirstBit m i)) (selectFn (myTestBit m i) i (i + 1))
        (myFirstBit m i) := rfl

theorem myFirstBit_spec (m N : ℕ) :
    (myFirstBit m N < N ∧ m.testBit (myFirstBit m N) = true ∧
        ∀ j < myFirstBit m N, m.testBit j = false) ∨
      (myFirstBit m N = N ∧ ∀ j < N, m.testBit j = false) := by
  induction N with
  | zero => exact Or.inr ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ i ih =>
    rw [myFirstBit_succ]
    rcases ih with ⟨hlt, htrue, hmin⟩ | ⟨heq, hall⟩
    · have hne : i - myFirstBit m i ≠ 0 := by omega
      have hz : isZero (i - myFirstBit m i) = 0 := by
        have hle := isZero_le_one (i - myFirstBit m i)
        rcases (show isZero (i - myFirstBit m i) = 0 ∨ isZero (i - myFirstBit m i) = 1 by omega)
          with h | h
        · exact h
        · exact absurd ((isZero_eq_one_iff _).mp h) hne
      rw [hz, selectFn_zero]
      exact Or.inl ⟨by omega, htrue, hmin⟩
    · have hz : isZero (i - myFirstBit m i) = 1 :=
        (isZero_eq_one_iff _).mpr (by omega)
      rw [hz, selectFn_one]
      have hle : myTestBit m i ≤ 1 := myTestBit.le_one m i
      rcases (show myTestBit m i = 0 ∨ myTestBit m i = 1 by omega) with hbit | hbit
      · rw [hbit, selectFn_zero]
        have hfalse : m.testBit i = false := by
          by_contra hcontra
          have := (myTestBit.eq_one_iff m i).mpr (by simpa using hcontra)
          omega
        refine Or.inr ⟨by omega, fun j hj => ?_⟩
        rcases (show j < i ∨ j = i by omega) with hlt' | heq'
        · exact hall j hlt'
        · subst heq'; exact hfalse
      · rw [hbit, selectFn_one]
        have htrue : m.testBit i = true := (myTestBit.eq_one_iff m i).mp hbit
        exact Or.inl ⟨by omega, htrue, fun j hj => hall j (by omega)⟩

theorem myFirstBit_lt {m N : ℕ} (h : ∃ ℓ < N, m.testBit ℓ = true) : myFirstBit m N < N := by
  rcases myFirstBit_spec m N with ⟨hlt, -, -⟩ | ⟨heq, hall⟩
  · exact hlt
  · obtain ⟨ℓ, hℓN, hℓtrue⟩ := h
    exact absurd hℓtrue (by simpa using hall ℓ hℓN)

theorem myFirstBit_testBit {m N : ℕ} (h : ∃ ℓ < N, m.testBit ℓ = true) :
    m.testBit (myFirstBit m N) = true := by
  rcases myFirstBit_spec m N with ⟨-, htrue, -⟩ | ⟨heq, hall⟩
  · exact htrue
  · obtain ⟨ℓ, hℓN, hℓtrue⟩ := h
    exact absurd hℓtrue (by simpa using hall ℓ hℓN)

theorem myClearBit_eq_xor {m ℓ : ℕ} (h : m.testBit ℓ = true) : myClearBit m ℓ = m ^^^ 2 ^ ℓ := by
  have hrlt : m % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt m (Nat.two_pow_pos ℓ)
  have h2 : (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hrlt2 : m % 2 ^ ℓ < 2 ^ (ℓ + 1) := by omega
  have hqr : m % 2 ^ (ℓ + 1) = 2 ^ ℓ + m % 2 ^ ℓ := by
    have hb : (m % 2 ^ (ℓ + 1)).testBit ℓ = true := by
      rw [Nat.testBit_mod_two_pow, h, decide_eq_true_iff.mpr (Nat.lt_succ_self ℓ), Bool.true_and]
    have hblt : m % 2 ^ (ℓ + 1) < 2 ^ (ℓ + 1) := Nat.mod_lt m (Nat.two_pow_pos (ℓ + 1))
    have hbge : 2 ^ ℓ ≤ m % 2 ^ (ℓ + 1) := by
      rcases Nat.lt_or_ge (m % 2 ^ (ℓ + 1)) (2 ^ ℓ) with hcon | hcon
      · exfalso
        rw [Nat.testBit_lt_two_pow hcon] at hb
        simp at hb
      · exact hcon
    have hmm : m % 2 ^ (ℓ + 1) % 2 ^ ℓ = m % 2 ^ ℓ :=
      Nat.mod_mod_of_dvd m (pow_dvd_pow 2 (Nat.le_succ ℓ))
    have hsub : m % 2 ^ (ℓ + 1) % 2 ^ ℓ = m % 2 ^ (ℓ + 1) - 2 ^ ℓ := by
      have heq2 : m % 2 ^ (ℓ + 1) = (m % 2 ^ (ℓ + 1) - 2 ^ ℓ) + 2 ^ ℓ := by omega
      calc m % 2 ^ (ℓ + 1) % 2 ^ ℓ
          = ((m % 2 ^ (ℓ + 1) - 2 ^ ℓ) + 2 ^ ℓ) % 2 ^ ℓ := by rw [← heq2]
        _ = (m % 2 ^ (ℓ + 1) - 2 ^ ℓ) % 2 ^ ℓ := Nat.add_mod_right _ _
        _ = m % 2 ^ (ℓ + 1) - 2 ^ ℓ := Nat.mod_eq_of_lt (by omega)
    omega
  have hclear : myClearBit m ℓ = 2 ^ (ℓ + 1) * (m / 2 ^ (ℓ + 1)) + m % 2 ^ ℓ := by
    have hdm := Nat.div_add_mod m (2 ^ (ℓ + 1))
    unfold myClearBit
    omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [hclear, Nat.testBit_two_pow_mul_add _ hrlt2 j, Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy j ℓ with hjl | hjl | hjl
  · rw [ite_eq_left (show j < ℓ + 1 by omega), Nat.testBit_mod_two_pow,
      decide_eq_true_iff.mpr hjl, decide_eq_false_iff_not.mpr (show ℓ ≠ j by omega)]
    simp
  · have hjt : m.testBit j = true := by rw [hjl]; exact h
    rw [ite_eq_left (show j < ℓ + 1 by omega), Nat.testBit_mod_two_pow,
      decide_eq_false_iff_not.mpr (show ¬ j < ℓ by omega), hjt,
      decide_eq_true_iff.mpr hjl.symm]
    rfl
  · rw [ite_eq_right (show ¬ j < ℓ + 1 by omega), Nat.testBit_div_two_pow,
      show j - (ℓ + 1) + (ℓ + 1) = j by omega, decide_eq_false_iff_not.mpr (show ℓ ≠ j by omega)]
    simp

theorem levelSet_splitVMin (n : ℕ) : levelSet (splitVMinLevel n) (splitVMinMask n) = VX n :=
  levelSet_minLevel (canonIdx n).unpair.1 (canonIdx n).unpair.2

theorem splitVMin_congr {n n' : ℕ} (hn : VX n = VX n') :
    splitVMinLevel n = splitVMinLevel n' ∧ splitVMinMask n = splitVMinMask n' := by
  have h : levelSet (canonIdx n).unpair.1 (canonIdx n).unpair.2 =
      levelSet (canonIdx n').unpair.1 (canonIdx n').unpair.2 := hn
  exact minLevel_unique h

theorem splitV_mask_nonempty (n : ℕ) :
    ∃ ℓ < 2 ^ (splitVMinLevel n + 1), (splitVUpsampled n).testBit ℓ = true := by
  have hne : (levelSet (splitVMinLevel n) (splitVMinMask n)).Nonempty := by
    rw [levelSet_splitVMin]; exact VX_nonempty n
  apply levelSet.nonempty_iff.mp
  show (levelSet (splitVMinLevel n + 1) (splitVUpsampled n)).Nonempty
  unfold splitVUpsampled
  rwa [levelSet.myUpsample (Nat.le_succ _)]

theorem splitV_bit_lt (n : ℕ) : splitVBit n < 2 ^ (splitVMinLevel n + 1) :=
  myFirstBit_lt (splitV_mask_nonempty n)

theorem splitV_bit_testBit (n : ℕ) : (splitVUpsampled n).testBit (splitVBit n) = true :=
  myFirstBit_testBit (splitV_mask_nonempty n)

theorem splitV_twin_testBit (n : ℕ) :
    (splitVUpsampled n).testBit (splitVBit n ^^^ 2 ^ splitVMinLevel n) = true := by
  set k := splitVMinLevel n with hk
  set m := splitVMinMask n with hm
  set ℓ₀ := splitVBit n with hℓ₀
  set M := splitVUpsampled n with hMdef
  have hlevelEq : levelSet (k + 1) M = levelSet k m := by
    rw [hMdef]; unfold splitVUpsampled; exact levelSet.myUpsample (Nat.le_succ k) m
  have hlt : ℓ₀ < 2 ^ (k + 1) := splitV_bit_lt n
  have hbit : M.testBit ℓ₀ = true := splitV_bit_testBit n
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hpos : (2 : ℕ) ^ k > 0 := Nat.two_pow_pos k
  have h2k : (2 : ℕ) ^ k < 2 ^ (k + 1) := by omega
  have htwinlt : ℓ₀ ^^^ 2 ^ k < 2 ^ (k + 1) := Nat.xor_lt_two_pow hlt h2k
  have hmod : (ℓ₀ ^^^ 2 ^ k) % 2 ^ k = ℓ₀ % 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
    rcases lt_or_ge i k with hik | hik
    · rw [decide_eq_true_iff.mpr hik, decide_eq_false_iff_not.mpr (show k ≠ i by omega),
        Bool.xor_false]
    · rw [decide_eq_false_iff_not.mpr (show ¬ i < k by omega)]
      simp
  have h1 : ℓ₀ ∈ levelSet k m := by
    have hM : ℓ₀ ∈ levelSet (k + 1) M := by
      rw [mem_levelSet, Nat.mod_eq_of_lt hlt]; exact hbit
    rwa [hlevelEq] at hM
  have h2' : (ℓ₀ ^^^ 2 ^ k) ∈ levelSet k m := by
    rw [mem_levelSet, hmod]
    rwa [mem_levelSet] at h1
  rw [← hlevelEq] at h2'
  rwa [mem_levelSet, Nat.mod_eq_of_lt htwinlt] at h2'

theorem xor_two_pow_ne_self (a k : ℕ) : a ^^^ 2 ^ k ≠ a := by
  have hb : (2 : ℕ) ^ k ≠ 0 := (Nat.two_pow_pos k).ne'
  intro h
  apply hb
  have h2 : a ^^^ (a ^^^ 2 ^ k) = a ^^^ a := by rw [h]
  simp [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h2

theorem splitV_left_nonempty (n : ℕ) :
    (levelSet (splitVMinLevel n + 1) (2 ^ splitVBit n)).Nonempty :=
  levelSet.nonempty_iff.mpr ⟨splitVBit n, splitV_bit_lt n, by simp⟩

theorem splitV_right_nonempty (n : ℕ) :
    (levelSet (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n))).Nonempty := by
  rw [myClearBit_eq_xor (splitV_bit_testBit n)]
  have h2 : (2 : ℕ) ^ (splitVMinLevel n + 1) = 2 * 2 ^ splitVMinLevel n := by
    rw [pow_succ]; ring
  have hpos : (2 : ℕ) ^ splitVMinLevel n > 0 := Nat.two_pow_pos _
  have h2k : (2 : ℕ) ^ splitVMinLevel n < 2 ^ (splitVMinLevel n + 1) := by omega
  refine levelSet.nonempty_iff.mpr
    ⟨splitVBit n ^^^ 2 ^ splitVMinLevel n,
      Nat.xor_lt_two_pow (splitV_bit_lt n) h2k, ?_⟩
  rw [Nat.testBit_xor, splitV_twin_testBit n, Nat.testBit_two_pow,
    decide_eq_false_iff_not.mpr (xor_two_pow_ne_self (splitVBit n) (splitVMinLevel n)).symm]
  rfl

theorem VX_splitVLeft (n : ℕ) :
    VX (splitVLeft n) = levelSet (splitVMinLevel n + 1) (2 ^ splitVBit n) := by
  have hne : (levelSet (splitVLeft n).unpair.1 (splitVLeft n).unpair.2).Nonempty := by
    unfold splitVLeft
    rw [unpair_pair_fst, unpair_pair_snd]
    exact splitV_left_nonempty n
  show levelSet (canonIdx (splitVLeft n)).unpair.1 (canonIdx (splitVLeft n)).unpair.2 = _
  rw [canonIdx.eq_self_of_nonempty hne]
  unfold splitVLeft
  rw [unpair_pair_fst, unpair_pair_snd]

theorem VX_splitVRight (n : ℕ) :
    VX (splitVRight n) =
      levelSet (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n)) := by
  have hne : (levelSet (splitVRight n).unpair.1 (splitVRight n).unpair.2).Nonempty := by
    unfold splitVRight
    rw [unpair_pair_fst, unpair_pair_snd]
    exact splitV_right_nonempty n
  show levelSet (canonIdx (splitVRight n)).unpair.1 (canonIdx (splitVRight n)).unpair.2 = _
  rw [canonIdx.eq_self_of_nonempty hne]
  unfold splitVRight
  rw [unpair_pair_fst, unpair_pair_snd]

theorem splitV_disjoint (n : ℕ) : VX (splitVLeft n) ∩ VX (splitVRight n) = ∅ := by
  rw [VX_splitVLeft, VX_splitVRight, myClearBit_eq_xor (splitV_bit_testBit n),
    levelSet.inter_same_level]
  ext i
  simp only [mem_levelSet, Set.mem_empty_iff_false, iff_false, Nat.testBit_and, Bool.and_eq_true]
  rintro ⟨h1, h2⟩
  have hpos : i % 2 ^ (splitVMinLevel n + 1) = splitVBit n := by
    by_contra hne'
    rw [Nat.testBit_two_pow] at h1
    exact hne' (of_decide_eq_true h1).symm
  rw [hpos, Nat.testBit_xor, splitV_bit_testBit n] at h2
  simp at h2

theorem splitV_union (n : ℕ) : VX (splitVLeft n) ∪ VX (splitVRight n) = VX n := by
  have hML : levelSet (splitVMinLevel n + 1) (splitVUpsampled n) = VX n := by
    unfold splitVUpsampled
    rw [levelSet.myUpsample (Nat.le_succ _)]
    exact levelSet_splitVMin n
  rw [VX_splitVLeft, VX_splitVRight, myClearBit_eq_xor (splitV_bit_testBit n),
    levelSet.union_same_level, ← hML]
  apply congrArg (levelSet (splitVMinLevel n + 1))
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor]
  rcases eq_or_ne i (splitVBit n) with rfl | hi
  · simp [splitV_bit_testBit n]
  · simp [Ne.symm hi]

theorem splitVLeft_eq_of_congr {n n' : ℕ} (hn : VX n = VX n') :
    splitVLeft n = splitVLeft n' := by
  obtain ⟨hlvl, hmask⟩ := splitVMin_congr hn
  have hups : splitVUpsampled n = splitVUpsampled n' := by
    unfold splitVUpsampled; rw [hlvl, hmask]
  have hbit : splitVBit n = splitVBit n' := by
    unfold splitVBit; rw [hups, hlvl]
  unfold splitVLeft
  rw [hlvl, hbit]

theorem splitVRight_eq_of_congr {n n' : ℕ} (hn : VX n = VX n') :
    splitVRight n = splitVRight n' := by
  obtain ⟨hlvl, hmask⟩ := splitVMin_congr hn
  have hups : splitVUpsampled n = splitVUpsampled n' := by
    unfold splitVUpsampled; rw [hlvl, hmask]
  have hbit : splitVBit n = splitVBit n' := by
    unfold splitVBit; rw [hups, hlvl]
  unfold splitVRight
  rw [hlvl, hups, hbit]

theorem splitVLeft_congr {n n' : ℕ} (hn : VX n = VX n') :
    VX (splitVLeft n) = VX (splitVLeft n') := by
  rw [splitVLeft_eq_of_congr hn]

theorem splitVRight_congr {n n' : ℕ} (hn : VX n = VX n') :
    VX (splitVRight n) = VX (splitVRight n') := by
  rw [splitVRight_eq_of_congr hn]

theorem myFirstBit_le (m N : ℕ) : myFirstBit m N ≤ N := by
  rcases myFirstBit_spec m N with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega

theorem primrec_myClearBit : Nat.Primrec (fun t => myClearBit t.unpair.1 t.unpair.2) := by
  have hpow : Nat.Primrec (fun t : ℕ => (2 : ℕ) ^ t.unpair.2) := primrec_two_pow Nat.Primrec.right
  exact (primrec_sub₂ Nat.Primrec.left hpow).of_eq fun _ => rfl

theorem primrec_myFirstBit : Nat.Primrec (fun t => myFirstBit t.unpair.1 t.unpair.2) := by
  have hm : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hsub : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 - w.unpair.2.unpair.2) :=
    primrec_sub₂ hi hih
  have htb : Nat.Primrec (fun w : ℕ => myTestBit w.unpair.1 w.unpair.2.unpair.1) :=
    (primrec.myTestBit.comp (hm.pair hi)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hsucc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 1) := Nat.Primrec.succ.comp hi
  have hGfn : Nat.Primrec (fun w =>
      selectFn (isZero (w.unpair.2.unpair.1 - w.unpair.2.unpair.2))
        (selectFn (myTestBit w.unpair.1 w.unpair.2.unpair.1) w.unpair.2.unpair.1
          (w.unpair.2.unpair.1 + 1))
        w.unpair.2.unpair.2) :=
    primrec_selectFn (primrec_isZero.comp hsub) (primrec_selectFn htb hi hsucc) hih
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

theorem primrec_splitVMinLevel : Nat.Primrec splitVMinLevel := by
  have hk : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.1) :=
    Nat.Primrec.left.comp primrec.canonIdx
  have hm : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.2) :=
    Nat.Primrec.right.comp primrec.canonIdx
  exact (primrec_minLevel.comp (hk.pair hm)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

theorem primrec_splitVMinMask : Nat.Primrec splitVMinMask := by
  have hk : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.1) :=
    Nat.Primrec.left.comp primrec.canonIdx
  have hm : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.2) :=
    Nat.Primrec.right.comp primrec.canonIdx
  exact (primrec_minMask.comp (hk.pair hm)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

theorem primrec_splitVUpsampled : Nat.Primrec splitVUpsampled := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  exact (primrec.myUpsample.comp
      (primrec_splitVMinLevel.pair (hk1.pair primrec_splitVMinMask))).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

theorem primrec_splitVBit : Nat.Primrec splitVBit := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hbound : Nat.Primrec (fun n : ℕ => (2 : ℕ) ^ (splitVMinLevel n + 1)) :=
    primrec_two_pow hk1
  exact (primrec_myFirstBit.comp (primrec_splitVUpsampled.pair hbound)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

theorem primrec_splitVLeft : Nat.Primrec splitVLeft := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hpow : Nat.Primrec (fun n : ℕ => (2 : ℕ) ^ splitVBit n) := primrec_two_pow primrec_splitVBit
  exact (Nat.Primrec.pair hk1 hpow).of_eq fun n => rfl

theorem primrec_splitVRight : Nat.Primrec splitVRight := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hclear : Nat.Primrec (fun n : ℕ => myClearBit (splitVUpsampled n) (splitVBit n)) :=
    (primrec_myClearBit.comp (primrec_splitVUpsampled.pair primrec_splitVBit)).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (Nat.Primrec.pair hk1 hclear).of_eq fun n => rfl

end DomainTheory.NeighbourhoodSystems
