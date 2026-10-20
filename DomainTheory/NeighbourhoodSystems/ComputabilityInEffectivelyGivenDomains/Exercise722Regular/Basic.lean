/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr

@[expose] public section

/-!
# Exercise 7.22 (Scott 1981, PRG-19, §7) — the regular-event layer

This file develops the **"regular events" hint** of Exercise 7.22 toward *effective givenness* of the
neighbourhood system `Ssys` of `Exercise722.lean`. Scott's hint:

> the sets in `S` are each "regular events" in the terminology of automata theory, and we have a
> decision method for the set algebra of regular events.

## What is mechanised here (green, choice-free)

We make the "regular event" content precise by giving `S` a finite **syntax** and a denotation, and
proving the syntax exactly captures `S`:

* `SExpr` — the syntax of `S`-terms: `Σ` (`sigma`), a singleton `{σ}` (`single σ`), concatenation
  `X·Y` (`cat`), and intersection `X ∩ Y` (`cap`). This is a *fragment* of regular expressions
  (closed under `·` and `∩`, with the universal language `Σ`), with **no** union, complement, or
  Kleene star — exactly Scott's four generators.
* `denote : SExpr → Set (List Bool)` — the language denoted by a term.
* **Decidable membership** `decide (w ∈ denote e)` via a `Bool` matcher `matchesB` with
  `matchesB_iff`, giving `DecidablePred (· ∈ denote e)` (choice-free). This is the computational core
  of "regular event": *membership of a word is decidable*.
* **Soundness/completeness**: `InS (denote e)` whenever `denote e` is non-empty
  (`InS_denote_of_nonempty`), and every member of `S` is a denotation (`InS_exists_denote`). Hence the
  exact characterization `InS X ↔ ∃ e, denote e = X ∧ X.Nonempty` (`inS_iff_exists_denote`).
* `SExpr` is countable (`Encodable SExpr`), so `S` is at most countable (Scott's standing finiteness).

## What remains for full effective givenness (Definition 7.1) — documented, not mechanised

Building a `ComputablePresentation`/`ScottPresentation Ssys` (Definition 7.1) requires Scott's two
relations to be **recursively decidable**, i.e. computed by genuine *primitive-recursive* functions
(`Domain.Recursive.RecDecidable = ∃ f, Nat.Primrec f ∧ …`); classical decidability does **not**
suffice. Over the syntax codes the two relations are:

* **(ii) consistency** `∃k. X_k ⊆ Xₙ ∩ Xₘ` ≡ (by positivity, Exercise 1.19 / `Ssys_isPositive`)
  **non-emptiness of `denote eₙ ∩ denote eₘ`** = non-emptiness of `denote (cap eₙ eₘ)`;
* **(i)** `Xₙ ∩ Xₘ = X_k` is **language equivalence** `denote (cap eₙ eₘ) = denote e_k`.

Both are decidable for regular events, but the decision procedures are **automata-complete**:

* *Emptiness* of an intersection genuinely needs the product-automaton reachability argument (there is
  no structural recursion for `∩`-emptiness: e.g. `Σ{0}Σ ∩ Σ{1}Σ` is non-empty while `{00} ∩ {11}`
  is empty), and a bounded-search emptiness test needs a *proven* state/length bound from a DFA.
* *Equivalence* is **not** reducible to intersection-emptiness inside this class, because the class is
  **not** closed under complement/difference (`L₁ ⊆ L₂ ⟺ L₁ \ L₂ = ∅` needs `\`). It requires a
  regular-language equivalence procedure (minimal DFAs / Myhill–Nerode, cf. `Example62Regular.lean`).

Mechanising those choice-free in `Recursive.lean` (a primitive-recursive subset construction +
reachability + a pumping/length bound, then `matchesB` over a bounded word set) is a separate, large
undertaking. Everything in *this* file is `⊆ {propext, Quot.sound}` (no `Classical.choice`).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-! ## Syntax and denotation -/

/- `deriving Encodable` builds a private auxiliary type, which a public instance cannot see.
This encoding is the public replacement: constructor tag in `Nat.pair`'s first component. -/
def sexprToNat : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (Encodable.encode σ)
  | .cat a b => Nat.pair 2 (Nat.pair (sexprToNat a) (sexprToNat b))
  | .cap a b => Nat.pair 3 (Nat.pair (sexprToNat a) (sexprToNat b))

theorem snd_lt_pair_of_pos_fst {a b : ℕ} (ha : 0 < a) : b < Nat.pair a b := by
  rw [Nat.pair]
  split_ifs with h
  · have hb : 0 < b := Nat.lt_trans ha h
    have hbb : b ≤ b * b := by
      calc
        b = 1 * b := (Nat.one_mul b).symm
        _ ≤ b * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hb)
    have : b * b < b * b + a := Nat.lt_add_of_pos_right ha
    omega
  · have : 0 < a * a + a := by
      have : a ≤ a * a + a := Nat.le_add_left _ _
      omega
    omega

/-- Decode with an explicit fuel bound so the recursion is structural. -/
def sexprOfNatFuel : ℕ → ℕ → Option SExpr
  | 0, _ => none
  | fuel + 1, n =>
    match n.unpair.1 with
    | 0 => some .sigma
    | 1 => (Encodable.decode n.unpair.2).map SExpr.single
    | 2 =>
      match sexprOfNatFuel fuel n.unpair.2.unpair.1, sexprOfNatFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match sexprOfNatFuel fuel n.unpair.2.unpair.1, sexprOfNatFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none

def sexprOfNat (n : ℕ) : Option SExpr := sexprOfNatFuel (n + 1) n

theorem sexprOfNatFuel_sexprToNat (e : SExpr) :
    ∀ fuel, sexprToNat e < fuel → sexprOfNatFuel fuel (sexprToNat e) = some e := by
  induction e with
  | sigma =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel => simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair]
  | single σ =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel => simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, Encodable.encodek]
  | cat a b iha ihb =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : sexprToNat a < fuel := by
        have hinner : sexprToNat a ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.left_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cat a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 2) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      have hb : sexprToNat b < fuel := by
        have hinner : sexprToNat b ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.right_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cat a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 2) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, iha _ ha, ihb _ hb]
  | cap a b iha ihb =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : sexprToNat a < fuel := by
        have hinner : sexprToNat a ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.left_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cap a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 3) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      have hb : sexprToNat b < fuel := by
        have hinner : sexprToNat b ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.right_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cap a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 3) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, iha _ ha, ihb _ hb]

instance : Encodable SExpr where
  encode := sexprToNat
  decode := sexprOfNat
  encodek e := sexprOfNatFuel_sexprToNat e (sexprToNat e + 1) (Nat.lt_succ_self _)

/-- The language denoted by an `S`-term. -/
def denote : SExpr → Set (List Bool)
  | .sigma => Set.univ
  | .single σ => {σ}
  | .cat a b => concat (denote a) (denote b)
  | .cap a b => denote a ∩ denote b

@[simp] theorem denote_sigma : denote .sigma = Set.univ := rfl
@[simp] theorem denote_single (σ : List Bool) : denote (.single σ) = {σ} := rfl
@[simp] theorem denote_cat (a b : SExpr) : denote (.cat a b) = concat (denote a) (denote b) := rfl
@[simp] theorem denote_cap (a b : SExpr) : denote (.cap a b) = denote a ∩ denote b := rfl

/-! ## Decidable word membership (the computational core of "regular event") -/

/-- A word `w` lies in a concatenation `X·Y` iff it splits as `w = w.take i ++ w.drop i` with the
prefix in `X` and the suffix in `Y` for some cut point `i ≤ |w|`. (The cut point is the length of
the `X`-part.) -/
theorem mem_concat_iff_split {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ i, i ≤ w.length ∧ w.take i ∈ X ∧ w.drop i ∈ Y := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a.length, by simp, ?_, ?_⟩
    · rw [List.take_left]; exact ha
    · rw [List.drop_left]; exact hb
  · rintro ⟨i, _, hpre, hsuf⟩
    exact ⟨w.take i, hpre, w.drop i, hsuf, w.take_append_drop i⟩

/-- The **`Bool` matcher** for `S`-terms: a structurally-recursive decision of word membership. The
concatenation case tries every cut point `i ∈ {0,…,|w|}`; the intersection case is the conjunction. -/
def matchesB : SExpr → List Bool → Bool
  | .sigma, _ => true
  | .single σ, w => decide (w = σ)
  | .cat a b, w => (List.range (w.length + 1)).any (fun i => matchesB a (w.take i) && matchesB b (w.drop i))
  | .cap a b, w => matchesB a w && matchesB b w

/-- **The matcher is correct**: `matchesB e w = true ↔ w ∈ denote e`. By structural induction on `e`;
the concatenation case unfolds `List.any` over the cut points and applies `mem_concat_iff_split`. -/
theorem matchesB_iff (e : SExpr) (w : List Bool) : matchesB e w = true ↔ w ∈ denote e := by
  induction e generalizing w with
  | sigma => simp [matchesB]
  | single σ => simp [matchesB]
  | cat a b iha ihb =>
    rw [denote_cat, mem_concat_iff_split]
    simp only [matchesB, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mp hi, (iha _).mp ha, (ihb _).mp hb⟩
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mpr hi, (iha _).mpr ha, (ihb _).mpr hb⟩
  | cap a b iha ihb =>
    simp only [matchesB, Bool.and_eq_true, denote_cap, Set.mem_inter_iff]
    rw [iha, ihb]

/-- **Membership in a regular event is decidable** (choice-free), via the matcher. -/
instance decidableMemDenote (e : SExpr) : DecidablePred (· ∈ denote e) :=
  fun w => decidable_of_iff (matchesB e w = true) (matchesB_iff e w)

/-! ## Soundness and completeness: the syntax captures exactly `S` -/

/-! ## Countability of `S`

`SExpr` is built from `List Bool` by finitely many constructors, hence countable; so `S`, being the
range of `denote` (restricted to non-empty denotations), is at most countable — Scott's standing
"at most a countable infinity of neighbourhoods" (Definition 7.1). -/

instance : Countable SExpr := inferInstance

/-! ## Reducing Definition 7.1's two relations to language equivalence on `SExpr`

The enumeration of `S` is (essentially) `n ↦ denote (decode n)` for codes `decode n : SExpr`. Over
such codes, Scott's two recursive-decidability obligations of Definition 7.1 become:

* **(ii)** consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` ≡ (positivity) `(denote eₙ ∩ denote eₘ).Nonempty`;
* **(i)** `Xₙ ∩ Xₘ = X_k` ≡ `denote (cap eₙ eₘ) = denote e_k`.

We show **both** are instances of *deciding language equivalence of two `SExpr`s* — and that emptiness
alone is therefore **not** enough (relation (i) needs the full equivalence test). -/

/-- The empty language is denotable in the fragment (it is **not** a member of `S`, which is
positive): `{0} ∩ {1} = ∅`. This is the canonical "`∅`" expression used to phrase emptiness as an
equivalence query. -/
def emptyExpr : SExpr := .cap (.single [false]) (.single [true])

@[simp] theorem denote_emptyExpr : denote emptyExpr = (∅ : Set (List Bool)) := by
  ext w
  simp only [emptyExpr, denote_cap, denote_single, Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  decide

/-! ## Why an emptiness decider is *not* enough (the concrete obstruction)

Relation (i) is genuine regular-language **equivalence**, which is strictly stronger than
fragment-emptiness, because the fragment is **not closed under complement / set-difference**
(`L₁ ⊆ L₂ ↔ L₁ \ L₂ = ∅` needs `\`). The following exhibit the obstruction concretely. -/

/-- "Contains a `0`" as a fragment expression: `Σ · {0} · Σ`. -/
def containsZero : SExpr := .cat .sigma (.cat (.single [false]) .sigma)
end Exercise722
end DomainTheory.NeighbourhoodSystems
