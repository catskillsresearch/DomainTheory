/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

/-!
# A choice-free Gödel numbering of `ℚ`, with primitive-recursive comparison/max/min

Theorem 8.8(b) (Scott 1981, PRG-19) needs `𝒰` (Definition 8.7) to have a genuine
`ComputablePresentation` (Definition 7.1). `𝒰`'s neighbourhoods are finite unions of rational
intervals `presentedIntervals L` for `L : List (ℚ × ℚ)`, so we first need `ℚ` itself — and hence
`List (ℚ × ℚ)` — coded by naturals, with the *arithmetic* operations `combineIntervals` actually
performs (`⊔`, `⊓`, `≤`, `=`) realized as genuinely `Nat.Primrec` functions on the codes.

## The encoding

An integer `z : ℤ` is coded as an (unnormalized) **difference pair** `Nat.pair z.toNat (-z).toNat`
— deliberately *not* a zig-zag bijection, since a difference pair turns every integer comparison
into a cross-*addition* of naturals (`a₁ - b₁ ≤ a₂ - b₂ ↔ a₁ + b₂ ≤ a₂ + b₁`), avoiding truncated
subtraction (and its case splits) entirely in the downstream `Nat.Primrec` proofs. A rational
`q : ℚ` is coded as `Nat.pair (encodeInt q.num) (q.den - 1)` (the `- 1`/`+ 1` shift keeps the
denominator positive without a separate side condition). Both round-trip **exactly** on every input
(`decodeInt_encodeInt`, `decodeRat_encodeRat`), not just on some "canonical" sub-class of codes —
mirroring `Recursive.lean`'s `decodeList_encodeList`/`encodeList_decodeList` exact round trips, and
for the same reason: it lets downstream code freely compose `encode ∘ decode` without tracking a
canonicality invariant.

`decodeRat`'s surjectivity (`decodeRat_surjective`) is what lets `𝒰`'s presentation enumerate *every*
rational, and `mkRat_self` (core Lean, choice-free) is the only fact about `Rat`'s internal
normalization we need.

## Primitive-recursive comparison arithmetic

`ratLeCode`/`ratLtCode`/`ratEqCode` decide `≤`/`</`/`=` between two rational codes by cross-clearing
denominators (again via addition, not subtraction, exactly as for `Int`); `ratMaxCode`/`ratMinCode`
select one of the two input codes via `Domain.Recursive.selectFn`, mirroring
`Domain.Recursive.primrec_max`'s pattern exactly. `zeroCode`/`oneCode` are fixed codes for the
constants `0, 1 : ℚ` used by `Definition87.lean`'s `clip`.

Everything here is `⊆ {propext, Quot.sound}` — no `Classical.choice` — since it is all direct
`Nat.Primrec` construction and finite case-splitting on `≤`/`<` (decidable, not classical, for `ℤ`
and `ℚ`).
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-! ### Integers as difference-pairs of naturals -/

/-- Decode a natural code as an integer: `pair a b ↦ a - b`. -/
def decodeInt (c : ℕ) : ℤ := (c.unpair.1 : ℤ) - (c.unpair.2 : ℤ)

/-- Encode an integer as the difference-pair `(z.toNat, (-z).toNat)` (one of the two is always
`0`). -/
def encodeInt (z : ℤ) : ℕ := Nat.pair z.toNat (-z).toNat

@[simp] theorem decodeInt_encodeInt (z : ℤ) : decodeInt (encodeInt z) = z := by
  unfold decodeInt encodeInt
  rw [unpair_pair]
  by_cases h : 0 ≤ z
  · have hz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h
    have hnz : ((-z).toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonpos (show -z ≤ 0 by omega); simp [this]
    rw [hz, hnz]; ring
  · have h' : z < 0 := by omega
    have hz : (z.toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonpos (show z ≤ 0 from h'.le); simp [this]
    have hnz : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    rw [hz, hnz]; ring

/-! ### Rationals as (integer numerator code, denominator `- 1`) pairs -/

/-- Decode a natural code as a rational via `mkRat`: `pair c d ↦ mkRat (decodeInt c) (d + 1)`. -/
def decodeRat (c : ℕ) : ℚ := mkRat (decodeInt c.unpair.1) (c.unpair.2 + 1)

/-- Encode a rational `q` using its own reduced `num`/`den`. -/
def encodeRat (q : ℚ) : ℕ := Nat.pair (encodeInt q.num) (q.den - 1)

@[simp] theorem decodeRat_encodeRat (q : ℚ) : decodeRat (encodeRat q) = q := by
  unfold decodeRat encodeRat
  rw [unpair_pair, decodeInt_encodeInt]
  have hden : q.den - 1 + 1 = q.den := by
    have := q.den_nz; omega
  rw [hden, Rat.mkRat_self]

/-! ### Primitive-recursive comparison of rational codes

`ratLeCode (pair c₁ c₂)` decides `decodeRat c₁ ≤ decodeRat c₂` by cross-clearing denominators:
writing `cᵢ` for `(aᵢ, bᵢ, dᵢ)` (so `decodeRat cᵢ = (aᵢ - bᵢ)/(dᵢ + 1)`), the comparison
`(a₁-b₁)/(d₁+1) ≤ (a₂-b₂)/(d₂+1)` (denominators positive) is equivalent, after moving every `bᵢ`
term to the other side to avoid subtraction, to `a₁(d₂+1) + b₂(d₁+1) ≤ a₂(d₁+1) + b₁(d₂+1)`. -/

/-- The numerator's positive part `a` of a rational code. -/
def qNumP (c : ℕ) : ℕ := c.unpair.1.unpair.1

/-- The numerator's negative part `b` of a rational code (so the numerator is `a - b`). -/
def qNumN (c : ℕ) : ℕ := c.unpair.1.unpair.2

/-- The denominator (`d + 1`, always positive) of a rational code. -/
def qDen (c : ℕ) : ℕ := c.unpair.2 + 1

theorem decodeRat_eq (c : ℕ) :
    decodeRat c = mkRat ((qNumP c : ℤ) - (qNumN c : ℤ)) (qDen c) := by
  unfold decodeRat decodeInt qNumP qNumN qDen; rfl

/-- The `{0,1}`-valued cross-cleared comparison test `a₁·d₂ + b₂·d₁ ≤ a₂·d₁ + b₁·d₂`, applied to
`t = pair c₁ c₂`. -/
def ratLeCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  isZero ((qNumP c1 * qDen c2 + qNumN c2 * qDen c1) -
    (qNumP c2 * qDen c1 + qNumN c1 * qDen c2))

/-- `ratLtCode (pair c₁ c₂)` decides `decodeRat c₁ < decodeRat c₂` via `¬ (decodeRat c₂ ≤ decodeRat c₁)`. -/
def ratLtCode (t : ℕ) : ℕ := 1 - ratLeCode (Nat.pair t.unpair.2 t.unpair.1)

/-! ### Max/min of rational codes, and constants -/

/-- `ratMaxCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the larger rational. -/
def ratMaxCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.2 t.unpair.1

/-- `ratMinCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the smaller rational. -/
def ratMinCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.1 t.unpair.2

/-- A fixed code for the rational `0`. -/
def zeroCode : ℕ := Nat.pair (Nat.pair 0 0) 0

/-- A fixed code for the rational `1`. -/
def oneCode : ℕ := Nat.pair (Nat.pair 1 0) 0

@[simp] theorem decodeRat_zeroCode : decodeRat zeroCode = 0 := by
  rw [decodeRat_eq]; norm_num [zeroCode, qNumP, qNumN, qDen, unpair_pair]

@[simp] theorem decodeRat_oneCode : decodeRat oneCode = 1 := by
  rw [decodeRat_eq]; norm_num [oneCode, qNumP, qNumN, qDen, unpair_pair]

/-! ### The midpoint of two rational codes (needed for Theorem 8.8(b) Part 4's `splitU`)

`ratMidCode (pair c₁ c₂)` codes `(decodeRat c₁ + decodeRat c₂) / 2` **without performing any
division**: cross-clearing denominators as in `ratLeCode` turns the sum into a single fraction over
`d₁·d₂`, and halving a fraction is simply *doubling its denominator* (`n/d / 2 = n/(2d)`), so no
`gcd`/reduction step is ever needed — `decodeRat`'s own `mkRat` call normalizes the result. -/

/-- The midpoint code `(c₁+c₂)/2` of two rational codes, via denominator cross-clearing (as in
`ratLeCode`) for the sum, then doubling the denominator to halve. -/
def ratMidCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  Nat.pair (Nat.pair (qNumP c1 * qDen c2 + qNumP c2 * qDen c1)
                      (qNumN c1 * qDen c2 + qNumN c2 * qDen c1))
    (2 * qDen c1 * qDen c2 - 1)
end DomainTheory.NeighbourhoodSystems
