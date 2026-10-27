module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vinter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


namespace myTestBit
open Domain.Recursive NeighborhoodSystem

theorem le_one (m ℓ : ℕ) : myTestBit m ℓ ≤ 1 := by
  unfold myTestBit
  rcases Nat.mod_two_eq_zero_or_one (myDivPow2 m ℓ) with h | h <;> omega

end myTestBit
open Domain.Recursive

/-- **`isPeriodicMask k j m ∈ {0,1}`** decides whether `levelSet k m` is also presentable at level
`j` via `m`'s own low bits (`isPeriodicMask_iff`), for `j ≤ k`. Meaningless (junk) for `j > k`,
exactly like `myUpsample` itself. -/
def isPeriodicMask (k j m : ℕ) : ℕ :=
  isZero ((myUpsample j k (myModPow2 m (2 ^ j)) - myModPow2 m (2 ^ k)) +
    (myModPow2 m (2 ^ k) - myUpsample j k (myModPow2 m (2 ^ j))))

/-- **`minLevel k m`**: the smallest `j ≤ k` such that `levelSet k m` is presentable at level `j`
(`minLevel_isPeriodicMask`, `minLevel_le`); the presentation-independent canonical level of the set
`levelSet k m` (`minLevel_unique`). -/
def minLevel (k m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (isPeriodicMask k i m) i (i + 1)) ih) (k + 1)

/-- The raw `Nat.rec`-fold underlying `minLevel k m`, exposed at an arbitrary bound `N` so the
inductive argument below can range over all `N`, specializing to `N = k + 1` at the end. -/
def minLevelFold (k m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (isPeriodicMask k i m) i (i + 1)) ih) N

/-- **`minMask k m`**: `m`'s own bits, truncated to `minLevel k m`'s width — the presentation-
independent canonical mask of the set `levelSet k m` (`minLevel_unique`). -/
def minMask (k m : ℕ) : ℕ := myModPow2 m (2 ^ minLevel k m)

theorem isPeriodicMask_le_one (k j m : ℕ) : isPeriodicMask k j m ≤ 1 := isZero_le_one _

theorem isPeriodicMask_eq_one_iff (k j m : ℕ) :
    isPeriodicMask k j m = 1 ↔ myUpsample j k (myModPow2 m (2 ^ j)) = myModPow2 m (2 ^ k) := by
  unfold isPeriodicMask
  rw [isZero_eq_one_iff]
  omega

/-- **The key correctness fact for `isPeriodicMask`**: it decides genuine presentability of
`levelSet k m` at the smaller level `j`, via `m`'s own bits. -/
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

/-- `levelSet k m` is trivially presentable at its own level `k` (the search's base case: the
bounded search for `minLevel` below always terminates by `j = k`). -/
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

/-- **The core invariant, by induction on the bound `N`** (mirrors `myFirstBit_spec` exactly). -/
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

/-- **`minLevel k m` genuinely witnesses presentability at its own value.** -/
theorem minLevel_isPeriodicMask (k m : ℕ) : isPeriodicMask k (minLevel k m) m = 1 := by
  rw [minLevel_eq_fold]
  rcases minLevelFold_spec k m (k + 1) with ⟨-, htrue, -⟩ | ⟨heq, hall⟩
  · exact htrue
  · exact absurd (isPeriodicMask_self k m) (hall k (by omega))

/-- **`minLevel k m` is minimal**: no smaller `j` witnesses presentability. -/
theorem minLevel_min {k m j : ℕ} (hj : j < minLevel k m) : isPeriodicMask k j m ≠ 1 := by
  revert hj
  rw [minLevel_eq_fold]
  intro hj
  rcases minLevelFold_spec k m (k + 1) with ⟨-, -, hmin⟩ | ⟨heq, hall⟩
  · exact hmin j hj
  · exact hall j (heq ▸ hj)

/-- **`(minLevel k m, minMask k m)` presents the same set as `(k, m)`.** -/
theorem levelSet_minLevel (k m : ℕ) : levelSet (minLevel k m) (minMask k m) = levelSet k m := by
  have h := (isPeriodicMask_iff (minLevel_le k m)).1 (minLevel_isPeriodicMask k m)
  show levelSet (minLevel k m) (myModPow2 m (2 ^ minLevel k m)) = levelSet k m
  rw [levelSet.myModPow2, h]

/-- **If `levelSet k m` is presentable at level `j ≤ k` via *any* mask `m'` at all, it is already
presentable there via the canonical witness `myModPow2 m (2 ^ j)` built from `m` alone.** The
genuinely new content of `(e)(d)(i)`: two direct specializations of the hypothesis (at `n = i` and
at `n = i % 2 ^ j`, for each bit position `i < 2 ^ k`) pin down `m`'s own bits without any
induction. -/
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

/-- **Restated via `isPeriodicMask`**: presentability at a smaller level `j ≤ k`, witnessed by
*any* mask, already shows up as `isPeriodicMask k j m = 1`. -/
theorem isPeriodicMask_of_presentable {k j m : ℕ} (hj : j ≤ k) {m' : ℕ}
    (h : levelSet j m' = levelSet k m) : isPeriodicMask k j m = 1 :=
  (isPeriodicMask_iff hj).2 (levelSet_presentable_imp_self hj h)

/-- **`minLevel` is presentation-independent**: two presentations of the same set have the same
minimal level. -/
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

/-- **`minMask` is presentation-independent**: two presentations of the same set have the same
minimal mask. Combined with `minLevel_eq`, this is `(e)(d)(i)`'s crux fact, delivering
`ComputableBisection.left_congr`/`right_congr` for `(e)(d)(ii)`'s rerouted split. -/
theorem minMask_eq {k₁ m₁ k₂ m₂ : ℕ} (h : levelSet k₁ m₁ = levelSet k₂ m₂) :
    minMask k₁ m₁ = minMask k₂ m₂ := by
  have hlvl := minLevel_eq h
  have hsets : levelSet (minLevel k₁ m₁) (minMask k₁ m₁) = levelSet (minLevel k₁ m₁) (minMask k₂ m₂) := by
    rw [levelSet_minLevel, hlvl, levelSet_minLevel, h]
  have hb1 : minMask k₁ m₁ < 2 ^ (2 ^ minLevel k₁ m₁) := myModPow2.lt _ _
  have hb2 : minMask k₂ m₂ < 2 ^ (2 ^ minLevel k₁ m₁) := hlvl ▸ myModPow2.lt _ _
  exact levelSet.inj_of_lt hb1 hb2 hsets

/-- **`minLevel_unique`**: the packaged crux fact — presentation-independence of both the minimal
level and the minimal mask. -/
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
  -- `w` is shaped `pair (pair k m) (pair i ih)`, matching `Nat.Primrec.prec`'s own convention
  -- (parameter `pair k m`, recursion variable `i`, accumulator `ih`).
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

/-- **The "clear one bit" primitive.** `myClearBit m ℓ := m - 2 ^ ℓ` — primitive recursive for
free (plain subtraction and a power of two), and, whenever bit `ℓ` of `m` is genuinely set,
literally equal to `m ^^^ 2 ^ ℓ` (`myClearBit_eq_xor`). -/
def myClearBit (m ℓ : ℕ) : ℕ := m - 2 ^ ℓ

/-- **The least-set-bit search combinator.** `myFirstBit m N` is the smallest `ℓ < N` with
`m.testBit ℓ = true`, or `N` itself (a sentinel, since a genuine witness is always `< N`) if no
such `ℓ` exists. Folds over `i = 0, 1, …, N - 1` in increasing order (via `Nat.rec` on `N`,
mirroring `bExistsFn`'s recursion exactly): once a witness has been found (the running value is
`< i`), it is carried forward unchanged; otherwise (`ih = i`, nothing found yet) bit `i` itself is
tested, becoming the new witness if set, or `i + 1` (the new sentinel) if not. -/
def myFirstBit (m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (myTestBit m i) i (i + 1)) ih) N

/-- The presentation-independent canonical level of `VX n`. -/
def splitVMinLevel (n : ℕ) : ℕ := minLevel (canonIdx n).unpair.1 (canonIdx n).unpair.2

/-- The presentation-independent canonical mask of `VX n`, at `splitVMinLevel n`'s width. -/
def splitVMinMask (n : ℕ) : ℕ := minMask (canonIdx n).unpair.1 (canonIdx n).unpair.2

/-- The upsampled mask `M := myUpsample k (k+1) m` for `(k, m) := (splitVMinLevel n, splitVMinMask
n)` — Scott's `M` from `V.no_minimal`, at the code level, fed the *minimal* presentation. -/
def splitVUpsampled (n : ℕ) : ℕ :=
  myUpsample (splitVMinLevel n) (splitVMinLevel n + 1) (splitVMinMask n)

/-- The splitting bit `ℓ₀` — the least set bit of the upsampled mask `M`, bounded by `2 ^ (k+1)`. -/
def splitVBit (n : ℕ) : ℕ :=
  myFirstBit (splitVUpsampled n) (2 ^ (splitVMinLevel n + 1))

/-- **`splitVLeft`**: the code for `Y := levelSet (k+1) (2 ^ ℓ₀)`, `V.no_minimal`'s "left" half. -/
def splitVLeft (n : ℕ) : ℕ := Nat.pair (splitVMinLevel n + 1) (2 ^ splitVBit n)

/-- **`splitVRight`**: the code for `Z := levelSet (k+1) (M ^^^ 2 ^ ℓ₀)`, `V.no_minimal`'s "right"
half — `myClearBit` stands in for `^^^` (justified since `ℓ₀` is, by construction, a genuinely set
bit of `M`; `myClearBit_eq_xor`, `(e)(b)(ii)`). -/
def splitVRight (n : ℕ) : ℕ :=
  Nat.pair (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n))

/-- **Unfolding equation** for `myFirstBit` at a successor argument, stated so `rw` fires cleanly
on the outer application (mirrors `LevelSetPrimrec.lean`'s `myUpsampleJointStep.eq`). -/
theorem myFirstBit_succ (m i : ℕ) :
    myFirstBit m (i + 1) =
      selectFn (isZero (i - myFirstBit m i)) (selectFn (myTestBit m i) i (i + 1))
        (myFirstBit m i) := rfl

/-- **The core invariant, by induction on `N`.** Either `myFirstBit m N` is a genuine witness
below `N` (`< N`, `testBit` true there, and no smaller index witnesses), or nothing witnesses
below `N` at all and `myFirstBit m N` sits exactly at the sentinel `N`. -/
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

/-- **`myFirstBit` finds a genuine witness whenever one exists below `N`.** -/
theorem myFirstBit_lt {m N : ℕ} (h : ∃ ℓ < N, m.testBit ℓ = true) : myFirstBit m N < N := by
  rcases myFirstBit_spec m N with ⟨hlt, -, -⟩ | ⟨heq, hall⟩
  · exact hlt
  · obtain ⟨ℓ, hℓN, hℓtrue⟩ := h
    exact absurd hℓtrue (by simpa using hall ℓ hℓN)

/-- **`myFirstBit m N` is genuinely a set bit of `m`, whenever a witness exists below `N`.** -/
theorem myFirstBit_testBit {m N : ℕ} (h : ∃ ℓ < N, m.testBit ℓ = true) :
    m.testBit (myFirstBit m N) = true := by
  rcases myFirstBit_spec m N with ⟨-, htrue, -⟩ | ⟨heq, hall⟩
  · exact htrue
  · obtain ⟨ℓ, hℓN, hℓtrue⟩ := h
    exact absurd hℓtrue (by simpa using hall ℓ hℓN)


/-- **`myClearBit` realizes `^^^ 2 ^ ℓ` whenever bit `ℓ` is genuinely set.** Proof: decompose `m`
around the boundary `2 ^ (ℓ + 1)` (`hqr`, via `Nat.div_add_mod`/`Nat.mod_mod_of_dvd` and a
single-wraparound `omega` argument, mirroring `LevelSetPrimrec.lean`'s own
`mod_eq_sub_of_le_of_lt_two_mul`), giving `myClearBit m ℓ = 2 ^ (ℓ+1) * (m / 2 ^ (ℓ+1)) + m % 2 ^
ℓ` (`hclear`); then `Nat.testBit_two_pow_mul_add` on both this and (implicitly, via `h`) on `m`
itself matches bit-for-bit against `Nat.testBit_xor`/`Nat.testBit_two_pow`'s case split on
`j`{`<`,`=`,`>`}`ℓ`. -/
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


/-- `(splitVMinLevel n, splitVMinMask n)` presents the same set as `canonIdx n`'s own pair, i.e.
`VX n` itself. -/
theorem levelSet_splitVMin (n : ℕ) : levelSet (splitVMinLevel n) (splitVMinMask n) = VX n :=
  levelSet_minLevel (canonIdx n).unpair.1 (canonIdx n).unpair.2

/-- **The presentation-independence of `splitVMinLevel`/`splitVMinMask`**: two codes presenting the
*same* `V`-set share the same minimal `(level, mask)` pair — the crux fact, via `MinLevel.lean`'s
`minLevel_unique`, that ultimately delivers `splitVLeft_congr`/`splitVRight_congr` below. -/
theorem splitVMin_congr {n n' : ℕ} (hn : VX n = VX n') :
    splitVMinLevel n = splitVMinLevel n' ∧ splitVMinMask n = splitVMinMask n' := by
  have h : levelSet (canonIdx n).unpair.1 (canonIdx n).unpair.2 =
      levelSet (canonIdx n').unpair.1 (canonIdx n').unpair.2 := hn
  exact minLevel_unique h


/-- `splitVUpsampled n`'s mask always has *some* set bit below `2^(k+1)` — inherited from
`VX n` always being non-empty (`VX_nonempty`), transported to the *minimal* presentation via
`levelSet_splitVMin`, then one level up via `levelSet.myUpsample`. Feeds
`myFirstBit_lt`/`myFirstBit_testBit`. -/
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

/-- **The twin-bit fact.** `myUpsample`'s duplication structure means *any* set bit `ℓ₀ < 2^(k+1)`
of the upsampled mask has a genuine twin at `ℓ₀ ^^^ 2^k` (also set): reduce both `ℓ₀` and its twin
mod `2^k` (they agree there, `hmod`, since `xor`-ing in `2^k` only ever touches bit `k`), then
transport the resulting `m`-level membership fact back up to `M`'s level via
`levelSet.myUpsample`. -/
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

/-- `ℓ₀ ^^^ 2 ^ k` is always genuinely different from `ℓ₀` (used to show `2 ^ ℓ₀` and `M ^^^ 2 ^
ℓ₀`'s witnessing bits are disjoint). -/
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

/-- **`splitVLeft` realizes `Y := levelSet (k+1) (2^ℓ₀)`**, `V.no_minimal`'s "left" half. -/
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

/-- **`splitVRight` realizes `Z := levelSet (k+1) (M ^^^ 2^ℓ₀)`**, `V.no_minimal`'s "right" half. -/
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

/-- **Exercise 8.12(e)(b), disjointness**: `splitVLeft`/`splitVRight` cover disjoint pieces —
transcribes `V.no_minimal`'s `hInter` verbatim. -/
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

/-- **Exercise 8.12(e)(b), covering**: `splitVLeft`/`splitVRight` reunite to `VX n` — transcribes
`V.no_minimal`'s `hUnion` verbatim. -/
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

/-- **`splitVLeft`'s raw index is presentation-independent** (stronger than `left_congr` needs):
two codes presenting the same `VX`-set produce the *literally identical* `splitVLeft` index, since
`splitVMin_congr` forces `splitVUpsampled`/`splitVBit` to agree exactly. -/
theorem splitVLeft_eq_of_congr {n n' : ℕ} (hn : VX n = VX n') :
    splitVLeft n = splitVLeft n' := by
  obtain ⟨hlvl, hmask⟩ := splitVMin_congr hn
  have hups : splitVUpsampled n = splitVUpsampled n' := by
    unfold splitVUpsampled; rw [hlvl, hmask]
  have hbit : splitVBit n = splitVBit n' := by
    unfold splitVBit; rw [hups, hlvl]
  unfold splitVLeft
  rw [hlvl, hbit]

/-- **`splitVRight`'s raw index is presentation-independent** (stronger than `right_congr` needs),
the same argument as `splitVLeft_eq_of_congr`. -/
theorem splitVRight_eq_of_congr {n n' : ℕ} (hn : VX n = VX n') :
    splitVRight n = splitVRight n' := by
  obtain ⟨hlvl, hmask⟩ := splitVMin_congr hn
  have hups : splitVUpsampled n = splitVUpsampled n' := by
    unfold splitVUpsampled; rw [hlvl, hmask]
  have hbit : splitVBit n = splitVBit n' := by
    unfold splitVBit; rw [hups, hlvl]
  unfold splitVRight
  rw [hlvl, hups, hbit]

/-- **`ComputableBisection.left_congr` for `splitVLeft`.** -/
theorem splitVLeft_congr {n n' : ℕ} (hn : VX n = VX n') :
    VX (splitVLeft n) = VX (splitVLeft n') := by
  rw [splitVLeft_eq_of_congr hn]

/-- **`ComputableBisection.right_congr` for `splitVRight`.** -/
theorem splitVRight_congr {n n' : ℕ} (hn : VX n = VX n') :
    VX (splitVRight n) = VX (splitVRight n') := by
  rw [splitVRight_eq_of_congr hn]

/-- **`myFirstBit` never overshoots its bound.** -/
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
end
