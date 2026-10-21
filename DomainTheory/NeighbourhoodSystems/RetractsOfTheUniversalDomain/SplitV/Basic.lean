/-ai
At a successor bound, the least-set-bit search selects the old value when a witness was already found, and otherwise selects the current index if its bit is set and the next sentinel if not.

The equation is the recursion by reflexivity.

Either the search value lies strictly below the bound, the bit there is set, and no smaller index is set, or the value equals the sentinel bound and no bit below the bound is set.

Proceed by induction on the bound. At zero the second alternative holds, since nothing is strictly below zero. At a successor, rewrite by the unfolding equation. If a witness was already found, the difference of the index and that witness is nonzero, so the zero-test of the difference is zero rather than one, and selecting on zero keeps the witness. If nothing was found, the running value equals the index, so the zero-test is one. The test bit is zero or one. If it is zero, the bit itself is unset, for otherwise the test-bit characterization would give one, and the sentinel alternative extends by splitting a smaller index into the old range or the current index. If it is one, the bit is set and the witness alternative holds at that index.

If some bit below the bound is set, the search value lies strictly below the bound.

The specification gives the bound in the witness alternative, and the sentinel alternative contradicts the existence of a set bit.

If some bit below the bound is set, the bit at the search value is set.

The specification gives that bit in the witness alternative, and the sentinel alternative again contradicts the hypothesis.

If bit ell of m is set, clearing that bit by subtraction equals exclusive or with two to the power ell.

The remainder modulo two to ell lies below that power, and below two to the power ell plus one. The remainder modulo the larger power equals two to ell plus the smaller remainder: its ell-th bit is still set, so it is at least two to ell, and reducing again modulo two to ell agrees with the original remainder because the powers divide, and that double remainder is the larger remainder minus two to ell. Division with remainder then rewrites the cleared value as the larger power times the quotient plus the smaller remainder. Compare bits. Below ell both sides read the remainder bit and exclusive or does not flip it. At ell the original bit is set, the remainder bit is unset, and exclusive or flips the power bit. Above ell the low window contributes nothing and the quotient bit is the original bit shifted by ell plus one, while exclusive or does not flip it.

The level set of the minimal level and minimal mask is the V-neighbourhood of n.

It is the minimal level set of the pair stored in the canonical index.

Codes presenting the same V-neighbourhood have the same minimal level and the same minimal mask.

Equality of the neighbourhoods is equality of the level sets of the two canonical pairs, and the minimal pair of a level set is unique.

The upsampled mask has some set bit strictly below two to the power of one more than the minimal level.

The minimal level set is nonempty because it equals the V-neighbourhood, which is nonempty. Passing one level up by upsampling preserves that nonempty level set, which is a set bit below the larger power.

The splitting bit lies strictly below that power.

The least-set-bit search returns a value below the bound once a set bit exists.

The splitting bit is set in the upsampled mask.

The least-set-bit search returns a set bit once a set bit exists.

The bit of the upsampled mask at the splitting bit combined by exclusive or with two to the minimal level is set.

Upsampling identifies the level set of the upsampled mask with the minimal level set. The splitting bit lies below the larger power and is set, and the twin index does too. The twin and the splitting bit have the same remainder modulo two to the minimal level, because exclusive or with that power changes only the bit at the level: below the level the bits agree, and at or above it both modular bits are unset. Membership of the splitting bit in the minimal level set therefore passes to the twin, and membership in the upsampled level set says the twin bit is set.

A natural number combined by exclusive or with a positive power of two is never equal to itself.

If it were, exclusive or on the left by the number, using associativity, exclusive or with itself, and exclusive or with zero, would make the power zero.

The level set one above the minimal level of the singleton mask two to the splitting bit is nonempty.

The splitting bit itself lies below the bound, and its bit in that power is set.

The level set of the cleared upsampled mask at that level is nonempty.

Rewrite the mask as exclusive or with the power of the splitting bit. The twin index lies below the larger power, and its bit in the exclusive or is set because the twin bit is set and the twin differs from the splitting bit, so the power bit there is unset.

The V-neighbourhood of the left half is the level set one above the minimal level of two to the splitting bit.

The pair stored by the left half presents a nonempty level set, so its canonical index is itself, and unpacking the pair is that level set.

The V-neighbourhood of the right half is the level set one above the minimal level of the cleared upsampled mask.

The pair stored by the right half presents a nonempty level set, so its canonical index is itself, and unpacking the pair is that level set.

The left and right V-halves are disjoint.

Rewrite both as those level sets, with clearing as exclusive or, and intersect level sets at the same level. A common element has both the power bit and the exclusive-or bit set at its remainder. The power bit forces the remainder to be the splitting bit, where exclusive or of the set bit with that power is unset.

The union of the left and right V-halves is the original V-neighbourhood.

The level set of the upsampled mask equals that neighbourhood, by upsampling and the minimal presentation. Rewrite the union as the union of the two level sets, with clearing as exclusive or. The masks agree bit by bit: at the splitting bit the original bit is set, and elsewhere the power contributes nothing, so the disjunction reproduces the original bit.

If two codes present the same V-neighbourhood, their left-half indices are equal.

The minimal levels and masks agree, so the upsampled masks agree, so the splitting bits agree, and rewriting those components in the left half gives the equality.

If two codes present the same V-neighbourhood, their right-half indices are equal.

The same agreement of minimal level, minimal mask, upsampled mask, and splitting bit rewrites every component of the right half.

If two codes present the same V-neighbourhood, the V-neighbourhoods of their left halves agree.

The raw left-half indices are equal.

If two codes present the same V-neighbourhood, the V-neighbourhoods of their right halves agree.

The raw right-half indices are equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.myFirstBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.myClearBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinMask
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVUpsampled
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVLeft
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVRight

@[expose] public section

/-!
# Exercise 8.12(e)(b)/(e)(d)(ii) (Scott 1981, PRG-19, Lecture VIII) — a computable canonical
bisection for `V`, rerouted through the minimal presentation

## 8.12(e)(b)(i): `myFirstBit`, the least-set-bit search combinator

`V_no_minimal`'s classical proof (`Exercise812.lean`) picks its splitting bit `ℓ₀` via a bare
existential (`levelSet_nonempty_iff.mp hne`). `LevelSetPrimrec.lean`'s existing `bExistsFn`
combinator only *decides* whether such a witness exists ({0,1}-valued); it never *produces* one.
`myFirstBit m N` fills that gap: the smallest `ℓ < N` with `m.testBit ℓ = true`, computed by the
same bounded `Nat.rec`-fold idiom `bExistsFn`/`bForallFn` use, but threading the witnessing index
itself through the recursion instead of a `{0,1}` flag — a sentinel value of `N` (never itself a
valid index `< N`) marks "no witness found among the indices scanned so far", exactly mirroring
`bExistsFn`'s own `0`-sentinel for "not yet found".
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-! ### `myFirstBit`: definition -/


/-! ### `myFirstBit`: primitive recursiveness -/

/-! ### `myFirstBit`: correctness -/

/-- **Unfolding equation** for `myFirstBit` at a successor argument, stated so `rw` fires cleanly
on the outer application (mirrors `LevelSetPrimrec.lean`'s `myUpsampleJointStep_eq`). -/
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
      have hle : myTestBit m i ≤ 1 := myTestBit_le_one m i
      rcases (show myTestBit m i = 0 ∨ myTestBit m i = 1 by omega) with hbit | hbit
      · rw [hbit, selectFn_zero]
        have hfalse : m.testBit i = false := by
          by_contra hcontra
          have := (myTestBit_eq_one_iff m i).mpr (by simpa using hcontra)
          omega
        refine Or.inr ⟨by omega, fun j hj => ?_⟩
        rcases (show j < i ∨ j = i by omega) with hlt' | heq'
        · exact hall j hlt'
        · subst heq'; exact hfalse
      · rw [hbit, selectFn_one]
        have htrue : m.testBit i = true := (myTestBit_eq_one_iff m i).mp hbit
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

/-! ## 8.12(e)(b)(ii): `myClearBit`, a computable "clear one bit" primitive

`V_no_minimal`'s classical proof needs `M ^^^ 2 ^ ℓ₀` (Mathlib's `Nat.xor`, not exposed as
`Nat.Primrec` — the reason `myLor`/`myUpsample` etc. had to be hand-built already, per
`LevelSetPrimrec.lean`'s own header). Since `ℓ₀` is always already known set in `M` at the point
of use (`myFirstBit_testBit`, `(e)(b)(i)`), a plain truncated subtraction suffices as the
computable stand-in: clearing a *known-set* bit is the same as subtracting its power of two.
`myClearBit_eq_xor` bridges the two, so every downstream argument can keep using Mathlib's own
`Nat.testBit_xor`/`Nat.testBit_two_pow` unchanged, exactly as `V_no_minimal`'s original proof
does. -/


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

/-! ## 8.12(e)(d)(ii): the minimal presentation of `VX n`, at the code level

`canonIdx n`'s raw `(level, mask)` pair is **not** a presentation-independent invariant of the set
`VX n` (`MinLevel.lean`'s header, `(e)(d)(i)`'s discovery) — the same set can be `canonIdx`-
canonical at arbitrarily many different levels via repeated `myUpsample`. `MinLevel.lean` supplies
the genuine invariant: `(minLevel, minMask)` applied to `canonIdx n`'s own pair. Every downstream
definition in this file is now built from `splitVMinLevel`/`splitVMinMask` (below) rather than
`(canonIdx n).unpair.1`/`.unpair.2` directly, so that `splitVLeft`/`splitVRight`'s *outputs* — in
fact, as it turns out, their raw *indices* (`splitVLeft_eq_of_congr`/`splitVRight_eq_of_congr`,
stronger than the `left_congr`/`right_congr` fields actually demand) — depend only on `VX n` as a
set, delivering `ComputableBisection.left_congr`/`right_congr` for `(e)(d)(iii)`. -/


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

/-! ## 8.12(e)(b)(iii): `splitVLeft`/`splitVRight` — the actual computable split

Follows `V_no_minimal`'s construction (`Exercise812.lean`, Scott's remark after Definition 8.7)
verbatim, at the code level: take `(k, m) := (splitVMinLevel n, splitVMinMask n)` — the *minimal*
presentation of `VX n` (`(e)(d)(ii)`; before the reroute this was `canonIdx n`'s own, possibly
non-minimal, pair) — upsample `m` one level finer (`M := myUpsample k (k+1) m`), pick the splitting
bit `ℓ₀` as `M`'s least set bit (`myFirstBit`, `(e)(b)(i)` — the classical proof instead draws `ℓ₀`
from a bare existential `levelSet_nonempty_iff.mp hne`, bounded by `2 ^ k`; here it is found
directly on the *upsampled* mask `M`, bounded by `2 ^ (k+1)`, which is fine since `upsample`
duplicates every set bit of `m` into a matching pair at level `k+1`, so *any* set bit of `M` has a
genuine "twin" — `(e)(b)(iv)`'s job to make precise). `splitVLeft`/`splitVRight` then package `Y :=
levelSet (k+1) (2^ℓ₀)` / `Z := levelSet (k+1) (M ^^^ 2^ℓ₀)` (`V_no_minimal`'s own `Y`/`Z`) as codes,
using `myClearBit` (`(e)(b)(ii)`) as the computable stand-in for `^^^`. -/


/-! ## 8.12(e)(b)(iv): correctness — `VX_splitVLeft`/`VX_splitVRight`, `splitV_disjoint`,
`splitV_union`

Transcribes `V_no_minimal`'s `hInter`/`hUnion` computations (`Exercise812.lean` lines 242–261) to
the `splitVLeft`/`splitVRight` code level, substituting `myFirstBit`'s spec for the classical
`hbit`/`ℓ₀` and `myClearBit_eq_xor` for the raw `^^^` occurrences. The one genuine addition beyond
a verbatim transcription: since `splitVBit`'s `ℓ₀` ranges over the *whole* `[0, 2^(k+1))` (found on
the upsampled mask `M` directly, per `(e)(b)(iii)`'s docstring) rather than being handed a priori
as `< 2^k` with a fixed twin `ℓ₀ + 2^k`, `splitV_twin_testBit` below establishes the general
twin-bit fact (`M`'s bit `ℓ₀ ^^^ 2^k` is set whenever bit `ℓ₀` is) needed for `VX_splitVRight`'s
nonemptiness — proved directly from `levelSet_myUpsample` (no fresh `testBit`-level `myUpsample`
lemma needed), by reducing both `ℓ₀` and its twin mod `2^k` and observing they agree there. -/

/-- `splitVUpsampled n`'s mask always has *some* set bit below `2^(k+1)` — inherited from
`VX n` always being non-empty (`VX_nonempty`), transported to the *minimal* presentation via
`levelSet_splitVMin`, then one level up via `levelSet_myUpsample`. Feeds
`myFirstBit_lt`/`myFirstBit_testBit`. -/
theorem splitV_mask_nonempty (n : ℕ) :
    ∃ ℓ < 2 ^ (splitVMinLevel n + 1), (splitVUpsampled n).testBit ℓ = true := by
  have hne : (levelSet (splitVMinLevel n) (splitVMinMask n)).Nonempty := by
    rw [levelSet_splitVMin]; exact VX_nonempty n
  apply levelSet_nonempty_iff.mp
  show (levelSet (splitVMinLevel n + 1) (splitVUpsampled n)).Nonempty
  unfold splitVUpsampled
  rwa [levelSet_myUpsample (Nat.le_succ _)]

theorem splitV_bit_lt (n : ℕ) : splitVBit n < 2 ^ (splitVMinLevel n + 1) :=
  myFirstBit_lt (splitV_mask_nonempty n)

theorem splitV_bit_testBit (n : ℕ) : (splitVUpsampled n).testBit (splitVBit n) = true :=
  myFirstBit_testBit (splitV_mask_nonempty n)

/-- **The twin-bit fact.** `myUpsample`'s duplication structure means *any* set bit `ℓ₀ < 2^(k+1)`
of the upsampled mask has a genuine twin at `ℓ₀ ^^^ 2^k` (also set): reduce both `ℓ₀` and its twin
mod `2^k` (they agree there, `hmod`, since `xor`-ing in `2^k` only ever touches bit `k`), then
transport the resulting `m`-level membership fact back up to `M`'s level via
`levelSet_myUpsample`. -/
theorem splitV_twin_testBit (n : ℕ) :
    (splitVUpsampled n).testBit (splitVBit n ^^^ 2 ^ splitVMinLevel n) = true := by
  set k := splitVMinLevel n with hk
  set m := splitVMinMask n with hm
  set ℓ₀ := splitVBit n with hℓ₀
  set M := splitVUpsampled n with hMdef
  have hlevelEq : levelSet (k + 1) M = levelSet k m := by
    rw [hMdef]; unfold splitVUpsampled; exact levelSet_myUpsample (Nat.le_succ k) m
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
  levelSet_nonempty_iff.mpr ⟨splitVBit n, splitV_bit_lt n, by simp⟩

theorem splitV_right_nonempty (n : ℕ) :
    (levelSet (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n))).Nonempty := by
  rw [myClearBit_eq_xor (splitV_bit_testBit n)]
  have h2 : (2 : ℕ) ^ (splitVMinLevel n + 1) = 2 * 2 ^ splitVMinLevel n := by
    rw [pow_succ]; ring
  have hpos : (2 : ℕ) ^ splitVMinLevel n > 0 := Nat.two_pow_pos _
  have h2k : (2 : ℕ) ^ splitVMinLevel n < 2 ^ (splitVMinLevel n + 1) := by omega
  refine levelSet_nonempty_iff.mpr
    ⟨splitVBit n ^^^ 2 ^ splitVMinLevel n,
      Nat.xor_lt_two_pow (splitV_bit_lt n) h2k, ?_⟩
  rw [Nat.testBit_xor, splitV_twin_testBit n, Nat.testBit_two_pow,
    decide_eq_false_iff_not.mpr (xor_two_pow_ne_self (splitVBit n) (splitVMinLevel n)).symm]
  rfl

/-- **`splitVLeft` realizes `Y := levelSet (k+1) (2^ℓ₀)`**, `V_no_minimal`'s "left" half. -/
theorem VX_splitVLeft (n : ℕ) :
    VX (splitVLeft n) = levelSet (splitVMinLevel n + 1) (2 ^ splitVBit n) := by
  have hne : (levelSet (splitVLeft n).unpair.1 (splitVLeft n).unpair.2).Nonempty := by
    unfold splitVLeft
    rw [unpair_pair_fst, unpair_pair_snd]
    exact splitV_left_nonempty n
  show levelSet (canonIdx (splitVLeft n)).unpair.1 (canonIdx (splitVLeft n)).unpair.2 = _
  rw [canonIdx_eq_self_of_nonempty hne]
  unfold splitVLeft
  rw [unpair_pair_fst, unpair_pair_snd]

/-- **`splitVRight` realizes `Z := levelSet (k+1) (M ^^^ 2^ℓ₀)`**, `V_no_minimal`'s "right" half. -/
theorem VX_splitVRight (n : ℕ) :
    VX (splitVRight n) =
      levelSet (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n)) := by
  have hne : (levelSet (splitVRight n).unpair.1 (splitVRight n).unpair.2).Nonempty := by
    unfold splitVRight
    rw [unpair_pair_fst, unpair_pair_snd]
    exact splitV_right_nonempty n
  show levelSet (canonIdx (splitVRight n)).unpair.1 (canonIdx (splitVRight n)).unpair.2 = _
  rw [canonIdx_eq_self_of_nonempty hne]
  unfold splitVRight
  rw [unpair_pair_fst, unpair_pair_snd]

/-- **Exercise 8.12(e)(b), disjointness**: `splitVLeft`/`splitVRight` cover disjoint pieces —
transcribes `V_no_minimal`'s `hInter` verbatim. -/
theorem splitV_disjoint (n : ℕ) : VX (splitVLeft n) ∩ VX (splitVRight n) = ∅ := by
  rw [VX_splitVLeft, VX_splitVRight, myClearBit_eq_xor (splitV_bit_testBit n),
    levelSet_inter_same_level]
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
`V_no_minimal`'s `hUnion` verbatim. -/
theorem splitV_union (n : ℕ) : VX (splitVLeft n) ∪ VX (splitVRight n) = VX n := by
  have hML : levelSet (splitVMinLevel n + 1) (splitVUpsampled n) = VX n := by
    unfold splitVUpsampled
    rw [levelSet_myUpsample (Nat.le_succ _)]
    exact levelSet_splitVMin n
  rw [VX_splitVLeft, VX_splitVRight, myClearBit_eq_xor (splitV_bit_testBit n),
    levelSet_union_same_level, ← hML]
  apply congrArg (levelSet (splitVMinLevel n + 1))
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor]
  rcases eq_or_ne i (splitVBit n) with rfl | hi
  · simp [splitV_bit_testBit n]
  · simp [Ne.symm hi]

/-! ## 8.12(e)(d)(ii): `splitVLeft_congr`/`splitVRight_congr`

The payoff of the reroute through `splitVMinLevel`/`splitVMinMask`: since `splitVMin_congr` shows
two codes presenting the *same* `VX`-set route through the identical minimal `(level, mask)` pair,
every downstream quantity built from it (`splitVUpsampled`, `splitVBit`, and hence `splitVLeft`/
`splitVRight` themselves) is *literally* the same raw index, not merely presenting the same set —
strictly stronger than the `ComputableBisection.left_congr`/`right_congr` fields actually demand,
proved first as `splitVLeft_eq_of_congr`/`splitVRight_eq_of_congr` below and then downgraded. -/

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
end DomainTheory.NeighbourhoodSystems
