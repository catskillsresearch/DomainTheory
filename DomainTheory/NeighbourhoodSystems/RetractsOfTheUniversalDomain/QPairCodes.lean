module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

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

/-- A fixed code for the rational `1`. -/
def oneCode : ℕ := Nat.pair (Nat.pair 1 0) 0

/-- The denominator (`d + 1`, always positive) of a rational code. -/
def qDen (c : ℕ) : ℕ := c.unpair.2 + 1

/-- The numerator's negative part `b` of a rational code (so the numerator is `a - b`). -/
def qNumN (c : ℕ) : ℕ := c.unpair.1.unpair.2

/-- The numerator's positive part `a` of a rational code. -/
def qNumP (c : ℕ) : ℕ := c.unpair.1.unpair.1

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

/-- `ratMaxCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the larger rational. -/
def ratMaxCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.2 t.unpair.1

/-- `ratMinCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the smaller rational. -/
def ratMinCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.1 t.unpair.2

/-- A fixed code for the rational `0`. -/
def zeroCode : ℕ := Nat.pair (Nat.pair 0 0) 0

@[simp] theorem decodeRat_zeroCode : decodeRat zeroCode = 0 := by
  rw [decodeRat_eq]; norm_num [zeroCode, qNumP, qNumN, qDen, unpair_pair]

@[simp] theorem decodeRat_oneCode : decodeRat oneCode = 1 := by
  rw [decodeRat_eq]; norm_num [oneCode, qNumP, qNumN, qDen, unpair_pair]

/-- The midpoint code `(c₁+c₂)/2` of two rational codes, via denominator cross-clearing (as in
`ratLeCode`) for the sum, then doubling the denominator to halve. -/
def ratMidCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  Nat.pair (Nat.pair (qNumP c1 * qDen c2 + qNumP c2 * qDen c1)
                      (qNumN c1 * qDen c2 + qNumN c2 * qDen c1))
    (2 * qDen c1 * qDen c2 - 1)

/-- `decodeRat` is surjective: every rational number is `decodeRat` of some code (namely
`encodeRat q`). -/
theorem decodeRat_surjective : Function.Surjective decodeRat :=
  fun q => ⟨encodeRat q, decodeRat_encodeRat q⟩

theorem primrec_qDen : Nat.Primrec qDen :=
  Nat.Primrec.succ.comp Nat.Primrec.right

theorem primrec_qNumN : Nat.Primrec qNumN := Nat.Primrec.right.comp Nat.Primrec.left

theorem primrec_qNumP : Nat.Primrec qNumP := Nat.Primrec.left.comp Nat.Primrec.left

theorem primrec_ratLeCode : Nat.Primrec ratLeCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hlhs : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hrhs : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.2 * qDen t.unpair.1 + qNumN t.unpair.1 * qDen t.unpair.2) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
      (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
  exact (primrec_isZero.comp (primrec_sub₂ hlhs hrhs)).of_eq fun t => by
    simp only [ratLeCode]

theorem primrec_ratLtCode : Nat.Primrec ratLtCode :=
  primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_ratLeCode.comp (Nat.Primrec.right.pair Nat.Primrec.left))

theorem primrec_ratMaxCode : Nat.Primrec ratMaxCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.right Nat.Primrec.left

theorem primrec_ratMidCode : Nat.Primrec ratMidCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hnumP : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumP t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
  have hnumN : Nat.Primrec (fun t : ℕ =>
      qNumN t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hden : Nat.Primrec (fun t : ℕ => 2 * qDen t.unpair.1 * qDen t.unpair.2 - 1) :=
    primrec_sub₂
      (primrec_mul₂ (primrec_mul₂ (Nat.Primrec.const 2) (primrec_qDen.comp hc1))
        (primrec_qDen.comp hc2))
      (Nat.Primrec.const 1)
  exact (Nat.Primrec.pair (Nat.Primrec.pair hnumP hnumN) hden).of_eq fun t => by
    simp only [ratMidCode]

theorem primrec_ratMinCode : Nat.Primrec ratMinCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.left Nat.Primrec.right

theorem qDen_pos (c : ℕ) : 0 < qDen c := Nat.succ_pos _

theorem qDen_ratMidCode (c1 c2 : ℕ) : qDen (ratMidCode (Nat.pair c1 c2)) = qDen c1 * qDen c2 * 2 := by
  have h1 : 1 ≤ 2 * qDen c1 * qDen c2 := by
    have hd1 := qDen_pos c1
    have hd2 := qDen_pos c2
    have : 0 < 2 * qDen c1 * qDen c2 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hd2
    omega
  show (ratMidCode (Nat.pair c1 c2)).unpair.2 + 1 = qDen c1 * qDen c2 * 2
  simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [Nat.sub_add_cancel h1]; ring

/-- **Correctness of `ratMidCode`**: it decodes to the arithmetic mean of the two decoded
rationals. -/
theorem decodeRat_ratMidCode (c1 c2 : ℕ) :
    decodeRat (ratMidCode (Nat.pair c1 c2)) = (decodeRat c1 + decodeRat c2) / 2 := by
  have hqnp : qNumP (ratMidCode (Nat.pair c1 c2)) =
      qNumP c1 * qDen c2 + qNumP c2 * qDen c1 := by
    show (ratMidCode (Nat.pair c1 c2)).unpair.1.unpair.1 = _
    simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  have hqnn : qNumN (ratMidCode (Nat.pair c1 c2)) =
      qNumN c1 * qDen c2 + qNumN c2 * qDen c1 := by
    show (ratMidCode (Nat.pair c1 c2)).unpair.1.unpair.2 = _
    simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_eq, hqnp, hqnn, qDen_ratMidCode, Rat.mkRat_eq_div,
    decodeRat_eq c1, decodeRat_eq c2, Rat.mkRat_eq_div, Rat.mkRat_eq_div]
  have hd1 : (qDen c1 : ℚ) ≠ 0 := by exact_mod_cast (qDen_pos c1).ne'
  have hd2 : (qDen c2 : ℚ) ≠ 0 := by exact_mod_cast (qDen_pos c2).ne'
  push_cast
  field_simp
  ring

/-- **`decodeRat_ratMidCode`, un-paired**: lets callers apply it to an arbitrary code `e`
(typically itself obtained by decoding a list, e.g. `firstElemCode`) without first having to
rewrite `e` as `Nat.pair e.unpair.1 e.unpair.2` in the ambient goal — doing that rewrite directly
on a term still containing `e` risks the `whnf`-blowup this project has hit before whenever `e`
is (or unfolds to) a large composite expression. -/
theorem decodeRat_ratMidCode' (e : ℕ) :
    decodeRat (ratMidCode e) = (decodeRat e.unpair.1 + decodeRat e.unpair.2) / 2 := by
  have h := decodeRat_ratMidCode e.unpair.1 e.unpair.2
  rwa [Nat.pair_unpair] at h

/-- **Correctness of `ratLeCode`**: it is `1` exactly when the decoded rationals compare `≤`. -/
theorem ratLeCode_eq_one_iff (c1 c2 : ℕ) :
    ratLeCode (Nat.pair c1 c2) = 1 ↔ decodeRat c1 ≤ decodeRat c2 := by
  unfold ratLeCode
  rw [unpair_pair_fst, unpair_pair_snd, isZero_eq_one_iff, Nat.sub_eq_zero_iff_le]
  rw [decodeRat_eq c1, decodeRat_eq c2, Rat.mkRat_eq_div, Rat.mkRat_eq_div,
    div_le_div_iff₀ (by exact_mod_cast qDen_pos c1) (by exact_mod_cast qDen_pos c2),
    ← Nat.cast_le (α := ℚ)]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

theorem ratLeCode_le_one (t : ℕ) : ratLeCode t ≤ 1 := isZero_le_one _

theorem decodeRat_ratMaxCode (c1 c2 : ℕ) :
    decodeRat (ratMaxCode (Nat.pair c1 c2)) = max (decodeRat c1) (decodeRat c2) := by
  unfold ratMaxCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, max_eq_right h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, max_eq_left ((not_le.mp h).le)]

theorem decodeRat_ratMinCode (c1 c2 : ℕ) :
    decodeRat (ratMinCode (Nat.pair c1 c2)) = min (decodeRat c1) (decodeRat c2) := by
  unfold ratMinCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, min_eq_left h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, min_eq_right ((not_le.mp h).le)]

theorem ratLtCode_eq_one_iff (c1 c2 : ℕ) :
    ratLtCode (Nat.pair c1 c2) = 1 ↔ decodeRat c1 < decodeRat c2 := by
  unfold ratLtCode
  rw [unpair_pair_fst, unpair_pair_snd]
  have h1 := ratLeCode_le_one (Nat.pair c2 c1)
  rw [show (1 : ℕ) - ratLeCode (Nat.pair c2 c1) = 1 ↔ ratLeCode (Nat.pair c2 c1) = 0 from by omega,
    show ratLeCode (Nat.pair c2 c1) = 0 ↔ ¬ ratLeCode (Nat.pair c2 c1) = 1 from by omega,
    ratLeCode_eq_one_iff, not_le]

theorem ratLtCode_le_one (t : ℕ) : ratLtCode t ≤ 1 := by unfold ratLtCode; omega

/-- **`<` on rational codes is recursively decidable.** Packaged as `RecDecidable₂` (rather than the
raw `{0,1}` characteristic `ratLtCode`) so it composes directly with `Recursive.lean`'s closure
lemmas (`.not`, `.and`, `.bExistsList`, `.swap`, ...). -/
theorem ratLtCode_recDecidable₂ : RecDecidable₂ (fun c1 c2 => decodeRat c1 < decodeRat c2) := by
  refine RecDecidable₂.of_paired_zero_one_char primrec_ratLtCode
    (fun t => by have := ratLtCode_le_one t; omega) (fun n m => ?_)
  exact (ratLtCode_eq_one_iff n m).symm


end DomainTheory.NeighbourhoodSystems
namespace Domain.Recursive
/-- `foldCode`'s step for consing the popped element `x` onto the accumulator (ignoring the
threaded parameter). -/
def consStep2 (w : ℕ) : ℕ := Nat.pair w.unpair.1 w.unpair.2.unpair.1 + 1

/-- `appendCode c1 c2` codes a list with the same **elements** as `decodeList c1 ++ decodeList c2`
(reversed on the `c1` side, since `foldCode` conses left-to-right; irrelevant for set-level uses). -/
def appendCode (c1 c2 : ℕ) : ℕ := foldCode consStep2 0 c2 c1

/-- `foldCode`'s step for the inner loop: pops `y` from `c2`, applies `bop (pair x y)` (`x` threaded
as the fixed parameter), conses onto the accumulator. -/
def crossInnerStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (bop (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1 + 1

/-- `crossInner bop x c2` codes `[bop (x, y) ∣ y ∈ decodeList c2]` (up to order). -/
def crossInner (bop : ℕ → ℕ) (x c2 : ℕ) : ℕ := foldCode (crossInnerStep bop) x 0 c2

/-- `foldCode`'s outer step: pops `x` from `c1`, appends `crossInner bop x c2` onto the
accumulator (`c2` threaded as the fixed parameter). -/
def crossOuterStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (crossInner bop w.unpair.1 w.unpair.2.unpair.2) w.unpair.2.unpair.1

/-- **`crossCombine bop c1 c2`** codes `[bop (x, y) ∣ x ∈ decodeList c1, y ∈ decodeList c2]`
(up to order/duplicates), i.e. the code-level analogue of `L1.flatMap (fun x => L2.map (bop x ·))`.
This is the workhorse behind `Definition87.lean`'s `combineIntervals` at the code level. -/
def crossCombine (bop : ℕ → ℕ) (c1 c2 : ℕ) : ℕ := foldCode (crossOuterStep bop) c2 0 c1

/-- `foldCode`'s step for `flatMapCode`: pops `y` from the folded list, appends `f (pair x y)`
(`x` threaded as the fixed parameter) onto the accumulator. -/
def flatMapStep (f : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (f (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1

/-- **`flatMapCode f x c`** codes `(decodeList c).flatMap (fun y => decodeList (f (pair x y)))`
(up to order/duplicates). -/
def flatMapCode (f : ℕ → ℕ) (x c : ℕ) : ℕ := foldCode (flatMapStep f) x 0 c

theorem consStep2_eq (x acc params : ℕ) :
    consStep2 (Nat.pair x (Nat.pair acc params)) = Nat.pair x acc + 1 := by
  unfold consStep2; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_appendCode_aux :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => consStep2 (Nat.pair x (Nat.pair acc 0))) acc l)
        ↔ z ∈ l ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, consStep2_eq, mem_decodeList_appendCode_aux l (Nat.pair a acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (hl | (rfl | hacc))
      · exact Or.inl (Or.inr hl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hacc
    · rintro ((rfl | hl) | hacc)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hl
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_appendCode (c1 c2 z : ℕ) :
    z ∈ decodeList (appendCode c1 c2) ↔ z ∈ decodeList c1 ∨ z ∈ decodeList c2 := by
  unfold appendCode
  rw [foldCode_eq', mem_decodeList_appendCode_aux (decodeList c1) c2 z]


theorem crossInnerStep_eq (bop : ℕ → ℕ) (y acc x : ℕ) :
    crossInnerStep bop (Nat.pair y (Nat.pair acc x)) = Nat.pair (bop (Nat.pair x y)) acc + 1 := by
  unfold crossInnerStep; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_crossInner_aux (bop : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList
          (List.foldl (fun acc y => crossInnerStep bop (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossInnerStep_eq,
      mem_decodeList_crossInner_aux bop x l (Nat.pair (bop (Nat.pair x a)) acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, heq⟩ | (rfl | hacc))
      · exact Or.inl ⟨y, Or.inr hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, rfl⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), heq⟩ | hacc)
      · exact Or.inr (Or.inl heq)
      · exact Or.inl ⟨y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossInner {bop : ℕ → ℕ} (x c2 z : ℕ) :
    z ∈ decodeList (crossInner bop x c2) ↔ ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossInner
  rw [foldCode_eq', mem_decodeList_crossInner_aux bop x (decodeList c2) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]


theorem crossOuterStep_eq (bop : ℕ → ℕ) (x acc c2 : ℕ) :
    crossOuterStep bop (Nat.pair x (Nat.pair acc c2)) = appendCode (crossInner bop x c2) acc := by
  unfold crossOuterStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_crossCombine_aux (bop : ℕ → ℕ) (c2 : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => crossOuterStep bop (Nat.pair x (Nat.pair acc c2)))
          acc l)
        ↔ (∃ x ∈ l, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossOuterStep_eq,
      mem_decodeList_crossCombine_aux bop c2 l (appendCode (crossInner bop a c2) acc) z,
      mem_decodeList_appendCode, mem_decodeList_crossInner]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨x, hx, y, hy, heq⟩ | (⟨y, hy, heq⟩ | hacc))
      · exact Or.inl ⟨x, Or.inr hx, y, hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, y, hy, heq⟩
      · exact Or.inr hacc
    · rintro (⟨x, (rfl | hx), y, hy, heq⟩ | hacc)
      · exact Or.inr (Or.inl ⟨y, hy, heq⟩)
      · exact Or.inl ⟨x, hx, y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)


theorem flatMapStep_eq (f : ℕ → ℕ) (y acc x : ℕ) :
    flatMapStep f (Nat.pair y (Nat.pair acc x)) = appendCode (f (Nat.pair x y)) acc := by
  unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_flatMapCode_aux (f : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc y => flatMapStep f (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z ∈ decodeList (f (Nat.pair x y))) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, flatMapStep_eq,
      mem_decodeList_flatMapCode_aux f x l (appendCode (f (Nat.pair x a)) acc) z,
      mem_decodeList_appendCode]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, hz⟩ | (hfa | hacc))
      · exact Or.inl ⟨y, Or.inr hy, hz⟩
      · exact Or.inl ⟨a, Or.inl rfl, hfa⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), hz⟩ | hacc)
      · exact Or.inr (Or.inl hz)
      · exact Or.inl ⟨y, hy, hz⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossCombine {bop : ℕ → ℕ} (c1 c2 z : ℕ) :
    z ∈ decodeList (crossCombine bop c1 c2) ↔
      ∃ x ∈ decodeList c1, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossCombine
  rw [foldCode_eq', mem_decodeList_crossCombine_aux bop c2 (decodeList c1) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

theorem mem_decodeList_flatMapCode {f : ℕ → ℕ} (x c z : ℕ) :
    z ∈ decodeList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, z ∈ decodeList (f (Nat.pair x y)) := by
  unfold flatMapCode
  rw [foldCode_eq', mem_decodeList_flatMapCode_aux f x (decodeList c) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

theorem primrec_consStep2 : Nat.Primrec consStep2 := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp (h1.pair h21)).of_eq fun _ => rfl

theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_consStep2 (Nat.Primrec.const 0) Nat.Primrec.right
    Nat.Primrec.left).of_eq fun _ => rfl

theorem primrec_crossInnerStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossInnerStep bop) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((hbop.comp (hx.pair hy)).pair hacc)).of_eq fun _ => rfl

theorem primrec_crossInner {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossInner bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossInnerStep hbop) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

theorem primrec_crossOuterStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossOuterStep bop) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hc2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun w : ℕ => crossInner bop w.unpair.1 w.unpair.2.unpair.2) :=
    ((primrec_crossInner hbop).comp (hx.pair hc2)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_appendCode.comp (hinner.pair hacc)).of_eq fun w => by
    unfold crossOuterStep
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_crossCombine {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossCombine bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossOuterStep hbop) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl

theorem primrec_flatMapStep {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (flatMapStep f) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (primrec_appendCode.comp ((hf.comp (hx.pair hy)).pair hacc)).of_eq fun w => by
    unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_flatMapCode {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec (fun t => flatMapCode f t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_flatMapStep hf) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

end Domain.Recursive
namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive

/-- Decode a natural as a pair of rationals. -/
def decodeRatPair (c : ℕ) : ℚ × ℚ := (decodeRat c.unpair.1, decodeRat c.unpair.2)

/-- Encode a pair of rationals as a single natural. -/
def encodeRatPair (p : ℚ × ℚ) : ℕ := Nat.pair (encodeRat p.1) (encodeRat p.2)

@[simp] theorem decodeRatPair_encodeRatPair (p : ℚ × ℚ) : decodeRatPair (encodeRatPair p) = p := by
  unfold decodeRatPair encodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_encodeRat]

/-- Decode a natural as a list of rational pairs. -/
def decodeQPairList (c : ℕ) : List (ℚ × ℚ) := (decodeList c).map decodeRatPair

/-- Encode a list of rational pairs as a single natural, via `encodeList`. -/
def encodeQPairList (L : List (ℚ × ℚ)) : ℕ := encodeList (L.map encodeRatPair)

@[simp] theorem decodeQPairList_encodeQPairList (L : List (ℚ × ℚ)) :
    decodeQPairList (encodeQPairList L) = L := by
  unfold decodeQPairList encodeQPairList
  rw [decodeList_encodeList, List.map_map]
  simp only [Function.comp_def, decodeRatPair_encodeRatPair, List.map_id_fun', id]

/-- Code-level `diffOneList`, taking `t = pair qc pc` (subtracted interval `q` **first**, matching
`flatMapCode`'s calling convention). -/
def diffOneCode (t : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1)))
    (Nat.pair (Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
      t.unpair.2.unpair.2) 0 + 1) + 1

/-- **Difference of a single interval-pair by another**, as a `≤ 2`-element list, via the
unconditional `Ico_diff_Ico`. -/
def diffOneList (p q : ℚ × ℚ) : List (ℚ × ℚ) := [(p.1, p.2 ⊓ q.1), (p.1 ⊔ q.2, p.2)]

/-- `diffSingleCode accL q` subtracts the single interval-pair coded by `q` from the whole
QPair-list coded by `accL`. -/
def diffSingleCode (accL q : ℕ) : ℕ := flatMapCode diffOneCode q accL

/-- `foldCode`'s step for `diffAllCode`'s fold over `L2` (params unused): pops `q`, subtracts it
from the "remaining pieces" accumulator via `diffSingleCode`. -/
def diffAllStep (w : ℕ) : ℕ := diffSingleCode w.unpair.2.unpair.1 w.unpair.1

/-- `diffAllCode pc L2` subtracts the whole QPair-list coded by `L2` from the single interval-pair
coded by `pc`, folding `diffSingleCode` over `L2` from the seed `[pc]`. -/
def diffAllCode (pc L2 : ℕ) : ℕ := foldCode diffAllStep 0 (Nat.pair pc 0 + 1) L2

/-- `diffCode c1 c2` subtracts the QPair-list coded by `c2` from the QPair-list coded by `c1`. -/
def diffCode (c1 c2 : ℕ) : ℕ := flatMapCode (fun t => diffAllCode t.unpair.2 t.unpair.1) c2 c1

/-- **Subtract a single interval-pair `q` from a whole presenting list `L`.** -/
def diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) : List (ℚ × ℚ) :=
  L.flatMap (fun p => diffOneList p q)

/-- **Subtract a whole presenting list `L2` from a single interval-pair `p`**, by folding
`diffSingleList` over `L2`, starting from `[p]`. -/
def diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L2.foldl diffSingleList [p]

/-- **Subtract `L2` from `L1`**, presenting the set difference `presentedIntervals L1 \\
presentedIntervals L2`. -/
def diffLists (L1 L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L1.flatMap (fun p => diffAllList p L2)

/-- The per-pair-code operation `(pc, qc) ↦ (max, min)` realizing `(p.1 ⊔ q.1, p.2 ⊓ q.2)`. -/
def qpCombineBop (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1))
    (ratMinCode (Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2))

/-- `combineCode` realizes `combineIntervals` on codes: `Nat.Primrec` in both arguments. -/
def combineCode (c1 c2 : ℕ) : ℕ := crossCombine qpCombineBop c1 c2

/-- The `{0,1}` flag: does the rational-pair code `e` decode to a non-degenerate pair `p.1 < p.2`? -/
def qpNonemptyBop (e : ℕ) : ℕ := ratLtCode (Nat.pair e.unpair.1 e.unpair.2)

/-- The `{0,1}` flag: does the QPair-list code `c` present a non-empty set? A bounded `∃` over
`decodeList c` via `Recursive.lean`'s `existsListChar` (the second argument of `existsListChar` is
an unused parameter, fixed to `0`). -/
def qpNonemptyChar (c : ℕ) : ℕ := existsListChar (fun t => qpNonemptyBop t.unpair.1) 0 c

/-- Two lists with the same **elements** present the same set. -/
theorem presentedIntervals_congr {L1 L2 : List (ℚ × ℚ)} (h : ∀ p, p ∈ L1 ↔ p ∈ L2) :
    presentedIntervals L1 = presentedIntervals L2 := by
  ext x
  simp only [mem_presentedIntervals]
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mp hp, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mpr hp, h1, h2⟩

/-- **Unconditional interval difference**: `Ico a b \ Ico c d = Ico a (b ⊓ c) ∪ Ico (a ⊔ d) b`, with
no ordering hypotheses on `a, b, c, d` (mirrors `Set.Ico_inter_Ico`'s unconditional intersection
formula). -/
theorem Ico_diff_Ico (a b c d : ℚ) :
    Set.Ico a b \ Set.Ico c d = Set.Ico a (b ⊓ c) ∪ Set.Ico (a ⊔ d) b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_union, lt_inf_iff, sup_le_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hcd⟩
    rcases lt_or_ge x c with hc | hc
    · exact Or.inl ⟨ha, hb, hc⟩
    · rcases lt_or_ge x d with hd | hd
      · exact absurd ⟨hc, hd⟩ hcd
      · exact Or.inr ⟨⟨ha, hd⟩, hb⟩
  · rintro (⟨ha, hb, hc⟩ | ⟨⟨ha, hd⟩, hb⟩)
    · exact ⟨⟨ha, hb⟩, fun ⟨hc', _⟩ => absurd hc' (not_le.mpr hc)⟩
    · exact ⟨⟨ha, hb⟩, fun ⟨_, hd'⟩ => absurd hd' (not_lt.mpr hd)⟩


theorem presentedIntervals_diffOneList (p q : ℚ × ℚ) :
    presentedIntervals (diffOneList p q) = Set.Ico p.1 p.2 \ Set.Ico q.1 q.2 := by
  unfold diffOneList
  rw [presentedIntervals_cons, presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]
  exact (Ico_diff_Ico p.1 p.2 q.1 q.2).symm


theorem presentedIntervals_diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) :
    presentedIntervals (diffSingleList L q) = presentedIntervals L \ Set.Ico q.1 q.2 := by
  induction L with
  | nil => simp [diffSingleList]
  | cons a l ih =>
    rw [show diffSingleList (a :: l) q = diffOneList a q ++ diffSingleList l q from rfl,
      presentedIntervals_append, presentedIntervals_diffOneList, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]


theorem decodeQPairList_diffOneCode (qc pc : ℕ) :
    decodeQPairList (diffOneCode (Nat.pair qc pc)) = diffOneList (decodeRatPair pc) (decodeRatPair qc) := by
  unfold diffOneCode decodeQPairList diffOneList decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeList_succ, decodeList_zero, List.map_cons,
    List.map_nil]
  rw [decodeRat_ratMinCode, decodeRat_ratMaxCode]

/-- **`flatMapCode`'s membership correctness, lifted to `decodeQPairList`.** -/
theorem mem_decodeQPairList_flatMapCode (f : ℕ → ℕ) (x c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, p ∈ decodeQPairList (f (Nat.pair x y)) := by
  unfold decodeQPairList
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_decodeList_flatMapCode] at hz
    obtain ⟨y, hy, hz'⟩ := hz
    exact ⟨y, hy, List.mem_map_of_mem hz'⟩
  · rintro ⟨y, hy, hp⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact ⟨e, (mem_decodeList_flatMapCode (f := f) x c e).mpr ⟨y, hy, he⟩, rfl⟩


theorem mem_decodeQPairList_diffSingleCode (accL q : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffSingleCode accL q) ↔ p ∈ diffSingleList (decodeQPairList accL) (decodeRatPair q) := by
  unfold diffSingleCode
  rw [mem_decodeQPairList_flatMapCode]
  simp only [decodeQPairList_diffOneCode]
  unfold diffSingleList decodeQPairList
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨decodeRatPair y, ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p', ⟨y, hy, rfl⟩, hp⟩; exact ⟨y, hy, hp⟩

theorem presentedIntervals_decodeQPairList_diffSingleCode (accL q : ℕ) :
    presentedIntervals (decodeQPairList (diffSingleCode accL q))
      = presentedIntervals (decodeQPairList accL) \ Set.Ico (decodeRatPair q).1 (decodeRatPair q).2 := by
  rw [presentedIntervals_congr (mem_decodeQPairList_diffSingleCode accL q), presentedIntervals_diffSingleList]


theorem diffAllStep_eq (acc x : ℕ) : diffAllStep (Nat.pair x (Nat.pair acc 0)) = diffSingleCode acc x := by
  unfold diffAllStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_foldl_diffAllStep (L2list : List ℕ) :
    ∀ acc : ℕ, presentedIntervals (decodeQPairList
        (List.foldl (fun acc x => diffAllStep (Nat.pair x (Nat.pair acc 0))) acc L2list))
      = presentedIntervals (decodeQPairList acc) \ presentedIntervals (L2list.map decodeRatPair) := by
  induction L2list with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, diffAllStep_eq, ih (diffSingleCode acc a),
      presentedIntervals_decodeQPairList_diffSingleCode, List.map_cons, presentedIntervals_cons,
      Set.sdiff_sdiff]

theorem presentedIntervals_decodeQPairList_diffAllCode (pc L2 : ℕ) :
    presentedIntervals (decodeQPairList (diffAllCode pc L2))
      = Set.Ico (decodeRatPair pc).1 (decodeRatPair pc).2 \ presentedIntervals (decodeQPairList L2) := by
  unfold diffAllCode
  rw [foldCode_eq', presentedIntervals_decodeQPairList_foldl_diffAllStep]
  unfold decodeQPairList
  simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero, List.map_cons,
    List.map_nil, presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]


theorem mem_decodeQPairList_diffCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffCode c1 c2) ↔ ∃ y ∈ decodeList c1, p ∈ decodeQPairList (diffAllCode y c2) := by
  unfold diffCode
  rw [mem_decodeQPairList_flatMapCode]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_flatMap_diffAllCode (c1list : List ℕ) (c2 : ℕ) :
    presentedIntervals (c1list.flatMap (fun y => decodeQPairList (diffAllCode y c2)))
      = presentedIntervals (c1list.map decodeRatPair) \ presentedIntervals (decodeQPairList c2) := by
  induction c1list with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, presentedIntervals_append,
      presentedIntervals_decodeQPairList_diffAllCode, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]

/-- **`diffCode` realizes `diffLists` (hence set difference) at the set level.** -/
theorem presentedIntervals_decodeQPairList_diffCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (diffCode c1 c2))
      = presentedIntervals (decodeQPairList c1) \ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_congr
      (fun p => (mem_decodeQPairList_diffCode c1 c2 p).trans (List.mem_flatMap).symm),
    presentedIntervals_decodeQPairList_flatMap_diffAllCode]
  rfl

/-- **A presented union of intervals is non-empty iff some pair in the list is itself non-degenerate**
(`p.1 < p.2`): every degenerate pair contributes the empty interval, and a single non-degenerate pair
already witnesses non-emptiness (via its left endpoint). -/
theorem presentedIntervals_nonempty_iff (L : List (ℚ × ℚ)) :
    (presentedIntervals L).Nonempty ↔ ∃ p ∈ L, p.1 < p.2 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp, hx1, hx2⟩ := mem_presentedIntervals.mp hx
    exact ⟨p, hp, lt_of_le_of_lt hx1 hx2⟩
  · rintro ⟨p, hp, hlt⟩
    exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hlt⟩⟩

theorem decodeRatPair_qpCombineBop (e1 e2 : ℕ) :
    decodeRatPair (qpCombineBop (Nat.pair e1 e2))
      = ((decodeRatPair e1).1 ⊔ (decodeRatPair e2).1, (decodeRatPair e1).2 ⊓ (decodeRatPair e2).2) := by
  unfold qpCombineBop decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode]

theorem mem_combineIntervals {L1 L2 : List (ℚ × ℚ)} {p : ℚ × ℚ} :
    p ∈ combineIntervals L1 L2 ↔ ∃ p1 ∈ L1, ∃ p2 ∈ L2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold combineIntervals
  rw [List.mem_flatMap]
  simp only [List.mem_map, eq_comm]

theorem mem_decodeQPairList (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList c ↔ ∃ e ∈ decodeList c, p = decodeRatPair e := by
  unfold decodeQPairList; rw [List.mem_map]; simp [eq_comm]

theorem mem_decodeQPairList_combineCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (combineCode c1 c2) ↔
      ∃ p1 ∈ decodeQPairList c1, ∃ p2 ∈ decodeQPairList c2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold decodeQPairList combineCode
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, hpz⟩
    rw [mem_decodeList_crossCombine] at hz
    obtain ⟨e1, he1, e2, he2, hze⟩ := hz
    refine ⟨decodeRatPair e1, List.mem_map_of_mem he1, decodeRatPair e2, List.mem_map_of_mem he2, ?_⟩
    rw [← hpz, hze, decodeRatPair_qpCombineBop]
  · rintro ⟨p1, hp1, p2, hp2, hp⟩
    obtain ⟨e1, he1, he1'⟩ := List.mem_map.mp hp1
    obtain ⟨e2, he2, he2'⟩ := List.mem_map.mp hp2
    refine ⟨qpCombineBop (Nat.pair e1 e2),
      (mem_decodeList_crossCombine (bop := qpCombineBop) c1 c2 _).mpr ⟨e1, he1, e2, he2, rfl⟩, ?_⟩
    rw [decodeRatPair_qpCombineBop, he1', he2', hp]

/-- **`combineCode` realizes `combineIntervals` at the set level.** -/
theorem presentedIntervals_decodeQPairList_combineCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (combineCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∩ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_inter]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_combineCode, mem_combineIntervals]

/-- **Subset between `presentedIntervals`-coded sets reduces to non-emptiness of `diffCode`.** -/
theorem presentedIntervals_decodeQPairList_subset_iff (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2) ↔
      ¬ (presentedIntervals (decodeQPairList (diffCode c1 c2))).Nonempty := by
  rw [presentedIntervals_decodeQPairList_diffCode, Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

theorem presentedIntervals_foldl_diffSingleList (L2 : List (ℚ × ℚ)) :
    ∀ acc : List (ℚ × ℚ),
      presentedIntervals (L2.foldl diffSingleList acc) = presentedIntervals acc \ presentedIntervals L2 := by
  induction L2 with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih (diffSingleList acc a), presentedIntervals_diffSingleList,
      presentedIntervals_cons, Set.sdiff_sdiff]

theorem presentedIntervals_diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffAllList p L2) = Set.Ico p.1 p.2 \ presentedIntervals L2 := by
  unfold diffAllList
  rw [presentedIntervals_foldl_diffSingleList, presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]

theorem presentedIntervals_diffLists (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffLists L1 L2) = presentedIntervals L1 \ presentedIntervals L2 := by
  induction L1 with
  | nil => simp [diffLists]
  | cons a l ih =>
    rw [show diffLists (a :: l) L2 = diffAllList a L2 ++ diffLists l L2 from rfl,
      presentedIntervals_append, presentedIntervals_diffAllList, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]

theorem primrec_diffOneCode : Nat.Primrec diffOneCode := by
  have ha : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hb : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hd : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hleft : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1))) :=
    ha.pair (primrec_ratMinCode.comp (hb.pair hc))
  have hright : Nat.Primrec (fun t : ℕ =>
      Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) t.unpair.2.unpair.2) :=
    (primrec_ratMaxCode.comp (ha.pair hd)).pair hb
  exact (Nat.Primrec.succ.comp (hleft.pair
    (Nat.Primrec.succ.comp (hright.pair (Nat.Primrec.const 0))))).of_eq fun _ => rfl

theorem primrec_diffSingleCode : Nat.Primrec (fun t : ℕ => diffSingleCode t.unpair.1 t.unpair.2) := by
  unfold diffSingleCode
  exact ((primrec_flatMapCode primrec_diffOneCode).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_diffAllStep : Nat.Primrec diffAllStep := by
  unfold diffAllStep
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hq : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  exact (primrec_diffSingleCode.comp (hacc.pair hq)).of_eq fun w => by
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_diffAllCode : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_diffAllStep (Nat.Primrec.const 0)
    (Nat.Primrec.succ.comp (Nat.Primrec.left.pair (Nat.Primrec.const 0)))
    Nat.Primrec.right).of_eq fun _ => rfl

theorem primrec_diffCode : Nat.Primrec (fun t : ℕ => diffCode t.unpair.1 t.unpair.2) := by
  unfold diffCode
  have hf : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.2 t.unpair.1) :=
    (primrec_diffAllCode.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((primrec_flatMapCode hf).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_qpCombineBop : Nat.Primrec qpCombineBop := by
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have h21 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h11.pair h21)).pair
    (primrec_ratMinCode.comp (h12.pair h22))).of_eq fun _ => rfl

theorem primrec_combineCode : Nat.Primrec (fun t => combineCode t.unpair.1 t.unpair.2) :=
  primrec_crossCombine primrec_qpCombineBop

theorem primrec_qpNonemptyBop : Nat.Primrec qpNonemptyBop :=
  primrec_ratLtCode.comp (Nat.Primrec.left.pair Nat.Primrec.right)

theorem primrec_qpNonemptyChar : Nat.Primrec qpNonemptyChar := by
  have hg : Nat.Primrec (fun t : ℕ => qpNonemptyBop t.unpair.1) :=
    primrec_qpNonemptyBop.comp Nat.Primrec.left
  exact ((primrec_existsListChar hg).comp (primrec_id.pair (Nat.Primrec.const 0))).of_eq
    fun c => by
      unfold qpNonemptyChar
      simp only [id, unpair_pair_fst, unpair_pair_snd]

theorem qpNonemptyBop_eq_one_iff (e : ℕ) :
    qpNonemptyBop e = 1 ↔ (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyBop decodeRatPair; exact ratLtCode_eq_one_iff e.unpair.1 e.unpair.2

theorem qpNonemptyChar_eq_one_iff (c : ℕ) :
    qpNonemptyChar c = 1 ↔ ∃ e ∈ decodeList c, (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyChar
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [unpair_pair_fst, qpNonemptyBop_eq_one_iff]

/-- **`presentedIntervals (decodeQPairList c)` is non-empty iff `qpNonemptyChar c = 1`.** -/
theorem presentedIntervals_decodeQPairList_nonempty_iff (c : ℕ) :
    (presentedIntervals (decodeQPairList c)).Nonempty ↔ qpNonemptyChar c = 1 := by
  rw [presentedIntervals_nonempty_iff, qpNonemptyChar_eq_one_iff]
  constructor
  · rintro ⟨p, hp, hlt⟩
    obtain ⟨e, he, rfl⟩ := (mem_decodeQPairList c p).mp hp
    exact ⟨e, he, hlt⟩
  · rintro ⟨e, he, hlt⟩
    exact ⟨decodeRatPair e, (mem_decodeQPairList c (decodeRatPair e)).mpr ⟨e, he, rfl⟩, hlt⟩

theorem qpNonemptyChar_le_one (c : ℕ) : qpNonemptyChar c ≤ 1 := existsListChar_le_one _ 0 c

/-- **Non-emptiness of the set presented by a QPair-list code is recursively decidable.** -/
theorem recDecidable_presentedIntervals_nonempty :
    RecDecidable (fun c => (presentedIntervals (decodeQPairList c)).Nonempty) :=
  RecDecidable.of_zero_one_char primrec_qpNonemptyChar
    (fun c => by have := qpNonemptyChar_le_one c; omega)
    presentedIntervals_decodeQPairList_nonempty_iff

/-- **Subset between `presentedIntervals`-coded sets is recursively decidable.** -/
theorem recDecidable₂_presentedIntervals_subset :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp primrec_diffCode).not
  exact presentedIntervals_decodeQPairList_subset_iff t.unpair.1 t.unpair.2

/-- **Equality between `presentedIntervals`-coded sets is recursively decidable**, from
`recDecidable₂_presentedIntervals_subset` in both directions (`Set.Subset.antisymm_iff`). -/
theorem recDecidable₂_presentedIntervals_eq :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) = presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable₂_presentedIntervals_subset.and recDecidable₂_presentedIntervals_subset.swap)
  exact Set.Subset.antisymm_iff


end DomainTheory.NeighbourhoodSystems
end
