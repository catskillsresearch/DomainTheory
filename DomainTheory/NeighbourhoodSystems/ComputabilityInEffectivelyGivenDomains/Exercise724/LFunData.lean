/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- Scott's set `Γ`, the *terminal* solution of `Γ = (⋃ᵢ {i} × Γ) ∪ {*}`: a finite sequence,
terminating at `*` (`Sum.inl`), or an infinite one that never terminates (`Sum.inr`). -/
abbrev Gamma : Type := List ℕ ⊕ (ℕ → ℕ)

/-- Scott's basepoint `*`: the empty (already-terminated) sequence. -/
def star : Gamma := Sum.inl []

/-- Prepend `i` to an infinite stream (`Stream'.cons`, spelled out by hand). -/
def streamCons (i : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => i
  | n + 1 => s n

@[simp] theorem streamCons_zero (i : ℕ) (s : ℕ → ℕ) : streamCons i s 0 = i := rfl

@[simp] theorem streamCons_succ (i : ℕ) (s : ℕ → ℕ) (n : ℕ) : streamCons i s (n + 1) = s n := rfl

/-- Scott's `(i, γ)`: prepend the natural `i` to a finite-or-infinite sequence `γ`. -/
def cons (i : ℕ) : Gamma → Gamma
  | .inl l => .inl (i :: l)
  | .inr s => .inr (streamCons i s)

/-- `*` is never of the shape `(i, γ)`. -/
theorem star_ne_cons (i : ℕ) (γ : Gamma) : star ≠ cons i γ := by
  cases γ <;> simp [star, cons]

/-- **`cons` is injective** (jointly in both arguments): `(i, γ) = (j, δ) ⟹ i = j ∧ γ = δ`. -/
theorem cons_injective {i j : ℕ} {γ δ : Gamma} (h : cons i γ = cons j δ) : i = j ∧ γ = δ := by
  cases γ with
  | inl l =>
    cases δ with
    | inl l' =>
      simp only [cons, Sum.inl.injEq, List.cons.injEq] at h
      exact ⟨h.1, by rw [h.2]⟩
    | inr s' => simp [cons] at h
  | inr s =>
    cases δ with
    | inl l' => simp [cons] at h
    | inr s' =>
      have heq : streamCons i s = streamCons j s' := by simpa [cons] using h
      have hi : i = j := by simpa using congrFun heq 0
      refine ⟨hi, ?_⟩
      have hs : s = s' := funext fun n => by simpa using congrFun heq (n + 1)
      rw [hs]

/-- Scott's `{i} × X`: the `i`-prefixed copy of a neighbourhood `X`. -/
def consSet (i : ℕ) (X : Set Gamma) : Set Gamma := {z | ∃ γ ∈ X, z = cons i γ}

@[simp] theorem mem_consSet {i : ℕ} {X : Set Gamma} {z : Gamma} :
    z ∈ consSet i X ↔ ∃ γ ∈ X, z = cons i γ := Iff.rfl

theorem consSet_subset_of_subset {i : ℕ} {X X' : Set Gamma} (h : X ⊆ X') :
    consSet i X ⊆ consSet i X' := by
  rintro z ⟨γ, hγ, rfl⟩; exact ⟨γ, h hγ, rfl⟩

/-- **`{i} × X ⊆ {i} × X' ↔ X ⊆ X'`.** -/
theorem consSet_subset {i : ℕ} {X X' : Set Gamma} :
    consSet i X ⊆ consSet i X' ↔ X ⊆ X' := by
  refine ⟨fun h γ hγ => ?_, consSet_subset_of_subset⟩
  obtain ⟨γ', hγ', heq⟩ := h ⟨γ, hγ, rfl⟩
  rwa [(cons_injective heq.symm).2] at hγ'

theorem consSet_inter (i : ℕ) (X X' : Set Gamma) :
    consSet i X ∩ consSet i X' = consSet i (X ∩ X') := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet]
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, γ', hγ', heq⟩
    obtain ⟨-, hγγ'⟩ := cons_injective heq
    exact ⟨γ, ⟨hγ, hγγ' ▸ hγ'⟩, rfl⟩
  · rintro ⟨γ, ⟨hγ, hγ'⟩, rfl⟩
    exact ⟨⟨γ, hγ, rfl⟩, ⟨γ, hγ', rfl⟩⟩

theorem consSet_inter_ne {i j : ℕ} (h : i ≠ j) (X Y : Set Gamma) :
    consSet i X ∩ consSet j Y = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨γ, -, rfl⟩ ⟨γ', -, heq⟩
  exact h (cons_injective heq).1

@[simp] theorem consSet_empty (i : ℕ) : consSet i (∅ : Set Gamma) = ∅ := by
  ext z; simp [mem_consSet]

theorem consSet_nonempty {i : ℕ} {X : Set Gamma} (h : X.Nonempty) : (consSet i X).Nonempty := by
  obtain ⟨γ, hγ⟩ := h; exact ⟨cons i γ, γ, hγ, rfl⟩

theorem star_not_mem_consSet (i : ℕ) (X : Set Gamma) : star ∉ consSet i X := by
  rintro ⟨γ, -, heq⟩; exact star_ne_cons i γ heq

/-- **The neighbourhood coded by a finite list.** `nbhd [] = Γ` (Scott's master `Γ`);
`nbhd (i :: l) = {i} × nbhd l`. Every `Lmem`-neighbourhood is `nbhd l` for a *unique* `l`
(`nbhd_injective`), mirroring `ExampleB.cone`/`Example62.embBit` generalized to `ℕ`-ary
branching. -/
def nbhd : List ℕ → Set Gamma
  | [] => Set.univ
  | i :: l => consSet i (nbhd l)

@[simp] theorem nbhd_nil : nbhd [] = (Set.univ : Set Gamma) := rfl

@[simp] theorem nbhd_cons (i : ℕ) (l : List ℕ) : nbhd (i :: l) = consSet i (nbhd l) := rfl

theorem nbhd_nonempty : ∀ l : List ℕ, (nbhd l).Nonempty
  | [] => ⟨star, trivial⟩
  | _ :: l => consSet_nonempty (nbhd_nonempty l)

/-- **The master reduction (mirrors `ExampleB.cone_subset_cone`).** `nbhd l ⊆ nbhd l' ↔ l' <+: l`:
cones reverse the prefix order. Proved by induction on `l`, peeling off matching heads. -/
theorem nbhd_subset_iff : ∀ (l l' : List ℕ), nbhd l ⊆ nbhd l' ↔ l' <+: l := by
  intro l
  induction l with
  | nil =>
    intro l'
    cases l' with
    | nil => simp
    | cons j t =>
      constructor
      · intro h
        exact absurd (h (Set.mem_univ star)) (by rw [nbhd_cons]; exact star_not_mem_consSet j (nbhd t))
      · rintro ⟨u, hu⟩
        simp at hu
  | cons i s ih =>
    intro l'
    cases l' with
    | nil => simp [nbhd_cons]
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rw [nbhd_cons, nbhd_cons, consSet_subset, ih t, List.cons_prefix_cons]
        simp
      · constructor
        · intro h
          exfalso
          obtain ⟨γ, hγ⟩ := nbhd_nonempty s
          have hmem : cons i γ ∈ consSet j (nbhd t) := h ⟨γ, hγ, rfl⟩
          obtain ⟨γ', -, heq⟩ := hmem
          exact hij (cons_injective heq).1
        · intro h
          rw [List.cons_prefix_cons] at h
          exact absurd h.1.symm hij

/-- **`nbhd` is injective.** Antisymmetry of `nbhd_subset_iff`: `l' <+: l` and `l <+: l'` force
`l.length = l'.length`, and a prefix of equal length is the whole list. -/
theorem nbhd_injective {l l' : List ℕ} (h : nbhd l = nbhd l') : l = l' := by
  have h1 : l' <+: l := (nbhd_subset_iff l l').mp h.subset
  have h2 : l <+: l' := (nbhd_subset_iff l' l).mp h.symm.subset
  exact (h1.eq_of_length (h1.length_le.antisymm h2.length_le)).symm

/-- Membership in Scott's system `L = {Γ} ∪ {{i} × X ∣ i ∈ ℕ, X ∈ L}`: `X ∈ L` iff `X = nbhd l`
for some finite list `l` (the "address" of the neighbourhood). -/
def Lmem (X : Set Gamma) : Prop := ∃ l, X = nbhd l

@[simp] theorem mem_nbhd (l : List ℕ) : Lmem (nbhd l) := ⟨l, rfl⟩

/-- **`L` is nested-or-disjoint** (Scott's "very special circumstance", generalizing
`ExampleB.cone_trichotomy`/`Example62`'s pairwise structure from `Bool` to `ℕ`-ary branching). -/
theorem L_nestedOrDisjoint : NestedOrDisjoint Lmem := by
  rintro X Y ⟨l, rfl⟩ ⟨l', rfl⟩
  induction l generalizing l' with
  | nil => exact Or.inr (Or.inl (by simp))
  | cons i s ih =>
    cases l' with
    | nil => exact Or.inl (by simp)
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rcases ih t with h1 | h2 | h3
        · exact Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h1)
        · exact Or.inr (Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h2))
        · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons, consSet_inter, h3, consSet_empty]))
      · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons]; exact consSet_inter_ne hij _ _))

/-- **Exercise 7.24 — `L` is a neighbourhood system** on tokens `Γ`, master `Γ = nbhd []`. -/
abbrev L : NeighborhoodSystem Gamma :=
  NeighborhoodSystem.ofNestedOrDisjoint Lmem Set.univ Set.univ_nonempty
    (mem_nbhd []) L_nestedOrDisjoint
    (fun {X} _ => Set.subset_univ X)

/-- **The `{0,1}` prefix test.** `isPrefixChar m n = 1 ↔ decodeList m <+: decodeList n`, built from
`Recursive.lean`'s `listLenChar`/`takeCode`/`listEqChar` (already primitive recursive): `l₁ <+: l₂`
iff `l₂.take l₁.length = l₁` (`List.prefix_iff_eq_take`), unconditionally (`List.take` auto-caps at
the available length, so no separate length guard is needed). -/
def isPrefixChar (m n : ℕ) : ℕ := listEqChar (takeCode (listLenChar m) n) m

theorem isPrefixChar_eq_one_iff (m n : ℕ) :
    isPrefixChar m n = 1 ↔ decodeList m <+: decodeList n := by
  unfold isPrefixChar
  rw [listEqChar_eq_one_iff, takeCode_eq, listLenChar_eq, List.prefix_iff_eq_take]
  exact eq_comm

theorem isPrefixChar_le_one (m n : ℕ) : isPrefixChar m n ≤ 1 := listEqChar_le_one _ _

theorem primrec_isPrefixChar : Nat.Primrec (fun t => isPrefixChar t.unpair.1 t.unpair.2) := by
  have hlen : Nat.Primrec (fun t : ℕ => listLenChar t.unpair.1) := primrec_listLenChar.comp Nat.Primrec.left
  have htake : Nat.Primrec (fun t : ℕ => takeCode (listLenChar t.unpair.1) t.unpair.2) :=
    (primrec_takeCode.comp (Nat.Primrec.pair hlen Nat.Primrec.right)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_listEqChar.comp (Nat.Primrec.pair htake Nat.Primrec.left)).of_eq fun t => by
    simp only [isPrefixChar, unpair_pair_fst, unpair_pair_snd]

/-- The enumeration `Lenum n := nbhd (decodeList n)`: every code `n` names the neighbourhood
addressed by its decoded list, and (via `encodeList`/`decodeList` round-tripping) this hits every
`Lmem` set. -/
def Lenum (n : ℕ) : Set Gamma := nbhd (decodeList n)

@[simp] theorem Lenum_mem (n : ℕ) : Lmem (Lenum n) := mem_nbhd (decodeList n)

theorem Lenum_surj {Y : Set Gamma} (hY : Lmem Y) : ∃ n, Lenum n = Y := by
  obtain ⟨l, rfl⟩ := hY
  exact ⟨encodeList l, by unfold Lenum; rw [decodeList_encodeList]⟩

/-- **`Xₙ ⊆ Xₘ` on the `Lenum` coding, decided by `isPrefixChar`.** -/
theorem Lenum_subset_iff (n m : ℕ) : Lenum n ⊆ Lenum m ↔ isPrefixChar m n = 1 := by
  unfold Lenum; rw [nbhd_subset_iff, isPrefixChar_eq_one_iff]

/-- **`Xₙ ∩ Xₘ = X_k` on the `Lenum` coding.** The intersection of two `nbhd`s is the more specific
of the two whenever they are nested, and no `Lmem` set at all otherwise (`nbhd` is always
nonempty, so `∅` never equals an `Lenum k`). -/
theorem Lenum_interEq_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  unfold Lenum
  rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
  · have hp : isPrefixChar m n = 1 := (isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_left.mpr h]
    constructor
    · intro heq; exact Or.inl ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨-, heq⟩ | ⟨hp', heq⟩)
      · rw [heq]
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList m) (decodeList n)).mpr hp')
  · have hp : isPrefixChar n m = 1 := (isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_right.mpr h]
    constructor
    · intro heq; exact Or.inr ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨hp', heq⟩ | ⟨-, heq⟩)
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList n) (decodeList m)).mpr hp')
      · rw [heq]
  · rw [h]
    have h1 : isPrefixChar m n ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList n))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ht ((nbhd_subset_iff _ _).mpr hp ht))
    have h2 : isPrefixChar n m ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList m))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ((nbhd_subset_iff _ _).mpr hp ht) ht)
    constructor
    · intro heq; exact absurd heq.symm (nbhd_nonempty (decodeList k)).ne_empty
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
      · exact absurd hp h1
      · exact absurd hp h2

/-- **7.1(ii) — consistency is recursively decidable.** `∃ k, Lenum k ⊆ Lenum n ∩ Lenum m` holds
iff `n, m` are nested (`isPrefixChar m n = 1 ∨ isPrefixChar n m = 1`): if nested, the more specific
of `n, m` itself witnesses it; conversely a common lower bound forces nestedness by
`L_nestedOrDisjoint` (a properly disjoint pair has no nonempty common lower bound, and every
`Lmem` set is nonempty). -/
theorem Lenum_cons_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
    · exact Or.inl ((isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h))
    · exact Or.inr ((isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h))
    · exfalso
      unfold Lenum at hk
      obtain ⟨t, ht⟩ := nbhd_nonempty (decodeList k)
      exact Set.notMem_empty t (h ▸ hk ht)
  · rintro (hp | hp)
    · exact ⟨n, Set.subset_inter subset_rfl ((Lenum_subset_iff n m).mpr hp)⟩
    · exact ⟨m, Set.subset_inter ((Lenum_subset_iff m n).mpr hp) subset_rfl⟩

/-- `isPrefixChar` composed with the swap of `unpair`, built via `.of_eq` (rather than relying
on elaborator defeq-unification against `Nat.pair`/`Nat.unpair`, which is expensive and can blow
the `whnf` budget). -/
theorem primrec_isPrefixChar_swap :
    Nat.Primrec (fun t => isPrefixChar t.unpair.2 t.unpair.1) :=
  (primrec_isPrefixChar.comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

/-- **The `{0,1}` consistency characteristic** — a flat `orBit` of the two `isPrefixChar`
directions (kept as a single hand-rolled arithmetic combinator rather than composing
`RecDecidable.or`/`.and`, per the project's course-of-values discipline: nesting the generic
`RecDecidable` combinators here elaborates a deeply-repeated composition and blows the `whnf`
budget). -/
def LenumConsChar (n m : ℕ) : ℕ :=
  isPrefixChar m n + isPrefixChar n m - isPrefixChar m n * isPrefixChar n m

private theorem isPrefixChar_eq_zero_or_one (m n : ℕ) :
    isPrefixChar m n = 0 ∨ isPrefixChar m n = 1 := by
  have := isPrefixChar_le_one m n; omega

theorem LenumConsChar_eq_one_iff (n m : ℕ) :
    LenumConsChar n m = 1 ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  unfold LenumConsChar
  rcases isPrefixChar_eq_zero_or_one m n with ha | ha <;>
    rcases isPrefixChar_eq_zero_or_one n m with hb | hb <;> simp [ha, hb]

theorem LenumConsChar_le_one (n m : ℕ) : LenumConsChar n m ≤ 1 := by
  unfold LenumConsChar
  rcases isPrefixChar_eq_zero_or_one m n with ha | ha <;>
    rcases isPrefixChar_eq_zero_or_one n m with hb | hb <;> simp [ha, hb]

theorem primrec_LenumConsChar :
    Nat.Primrec (fun t => LenumConsChar t.unpair.1 t.unpair.2) := by
  have ha : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.2 t.unpair.1) :=
    primrec_isPrefixChar_swap
  have hb : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.1 t.unpair.2) := primrec_isPrefixChar
  exact (primrec_sub₂ (primrec_add₂ ha hb) (primrec_mul₂ ha hb)).of_eq fun t => by
    simp only [LenumConsChar]

/-- Named-function packaging of `LenumConsChar` on `Nat.pair`-coded pairs (same rationale as
`LenumSubsetChar` above: avoids elaborator defeq-unification against `Nat.pair`/`Nat.unpair`). -/
def LenumConsCharP (t : ℕ) : ℕ := LenumConsChar t.unpair.1 t.unpair.2

theorem primrec_LenumConsCharP : Nat.Primrec LenumConsCharP :=
  primrec_LenumConsChar.of_eq fun t => by simp only [LenumConsCharP]

theorem LenumConsCharP_le_one (t : ℕ) : LenumConsCharP t ≤ 1 :=
  LenumConsChar_le_one _ _

theorem Lenum_cons_charP_eq_one_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ LenumConsCharP (Nat.pair n m) = 1 := by
  unfold LenumConsCharP
  rw [unpair_pair_fst, unpair_pair_snd, LenumConsChar_eq_one_iff]
  exact Lenum_cons_iff n m

/-- **7.1(ii) — consistency is recursively decidable.** -/
theorem Lenum_cons_computable : RecDecidable₂ (fun n m => ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :=
  RecDecidable₂.of_paired_zero_one_char primrec_LenumConsCharP
    (fun t => by have := LenumConsCharP_le_one t; omega)
    Lenum_cons_charP_eq_one_iff

/-- **The `{0,1}` intersection-equality characteristic** — same flat-`orBit` discipline as
`LenumConsChar`. -/
def LenumInterEqChar (n m k : ℕ) : ℕ :=
  mulBit (isPrefixChar m n) (listEqChar k n) + mulBit (isPrefixChar n m) (listEqChar k m)
    - mulBit (isPrefixChar m n) (listEqChar k n) * mulBit (isPrefixChar n m) (listEqChar k m)

private theorem mulBit_eq_zero_or_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    mulBit a b = 0 ∨ mulBit a b = 1 := by
  have := mulBit_le_one ha hb; omega

theorem LenumInterEqChar_eq_one_iff (n m k : ℕ) :
    LenumInterEqChar n m k = 1 ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  have hstep : LenumInterEqChar n m k = 1 ↔
      mulBit (isPrefixChar m n) (listEqChar k n) = 1 ∨
      mulBit (isPrefixChar n m) (listEqChar k m) = 1 := by
    unfold LenumInterEqChar
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
      rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
        simp [ha, hb]
  rw [hstep, mulBit_eq_one_iff, mulBit_eq_one_iff, listEqChar_eq_one_iff, listEqChar_eq_one_iff]

theorem LenumInterEqChar_le_one (n m k : ℕ) : LenumInterEqChar n m k ≤ 1 := by
  unfold LenumInterEqChar
  rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
      simp [ha, hb]

theorem primrec_LenumInterEqChar :
    Nat.Primrec (fun t => LenumInterEqChar t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hpmn : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.2.unpair.1 t.unpair.1) :=
    (primrec_isPrefixChar.comp (Nat.Primrec.pair hm hn)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hpnm : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_isPrefixChar.comp (Nat.Primrec.pair hn hm)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hekn : Nat.Primrec (fun t : ℕ => listEqChar t.unpair.2.unpair.2 t.unpair.1) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hk hn)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hekm : Nat.Primrec (fun t : ℕ => listEqChar t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hk hm)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have ha : Nat.Primrec (fun t : ℕ => mulBit (isPrefixChar t.unpair.2.unpair.1 t.unpair.1)
      (listEqChar t.unpair.2.unpair.2 t.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair hpmn hekn)).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hb : Nat.Primrec (fun t : ℕ => mulBit (isPrefixChar t.unpair.1 t.unpair.2.unpair.1)
      (listEqChar t.unpair.2.unpair.2 t.unpair.2.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair hpnm hekm)).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_sub₂ (primrec_add₂ ha hb) (primrec_mul₂ ha hb)).of_eq fun t => by
    simp only [LenumInterEqChar]

/-- Named-function packaging of `LenumInterEqChar` on `Nat.pair (Nat.pair)`-coded triples (same
rationale as `LenumSubsetChar`/`LenumConsCharP` above). -/
def LenumInterEqCharP (t : ℕ) : ℕ :=
  LenumInterEqChar t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2

theorem primrec_LenumInterEqCharP : Nat.Primrec LenumInterEqCharP :=
  primrec_LenumInterEqChar.of_eq fun t => by simp only [LenumInterEqCharP]

theorem LenumInterEqCharP_le_one (t : ℕ) : LenumInterEqCharP t ≤ 1 :=
  LenumInterEqChar_le_one _ _ _

theorem Lenum_interEq_charP_eq_one_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔ LenumInterEqCharP (Nat.pair n (Nat.pair m k)) = 1 := by
  unfold LenumInterEqCharP
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [LenumInterEqChar_eq_one_iff]
  exact Lenum_interEq_iff n m k

/-- **7.1(i) — `Xₙ ∩ Xₘ = X_k` is recursively decidable.** -/
theorem Lenum_interEq_computable : RecDecidable₃ (fun n m k => Lenum n ∩ Lenum m = Lenum k) :=
  RecDecidable₃.of_triple_zero_one_char primrec_LenumInterEqCharP
    (fun t => by have := LenumInterEqCharP_le_one t; omega)
    Lenum_interEq_charP_eq_one_iff

/-- The master neighbourhood is coded by `0` (`decodeList 0 = []`). -/
theorem Lenum_zero : Lenum 0 = Set.univ := by unfold Lenum; rw [decodeList_zero]; rfl

def LenumInter (n m : ℕ) : ℕ := selectFn (isPrefixChar m n) n m

theorem primrec_LenumInter : Nat.Primrec (fun t => LenumInter t.unpair.1 t.unpair.2) :=
  (primrec_selectFn primrec_isPrefixChar_swap Nat.Primrec.left Nat.Primrec.right).of_eq
    fun t => by simp only [LenumInter]

theorem LenumInter_spec {n m : ℕ} (h : ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :
    Lenum (LenumInter n m) = Lenum n ∩ Lenum m := by
  unfold LenumInter
  rcases isPrefixChar_eq_zero_or_one m n with h0 | h1
  · rw [h0, selectFn_zero]
    have hp : isPrefixChar n m = 1 := by
      rcases (Lenum_cons_iff n m).mp h with hp | hp
      · rw [h0] at hp; exact absurd hp (by decide)
      · exact hp
    exact (Set.inter_eq_right.mpr ((Lenum_subset_iff m n).mpr hp)).symm
  · rw [h1, selectFn_one]
    exact (Set.inter_eq_left.mpr ((Lenum_subset_iff n m).mpr h1)).symm

/-- **Exercise 7.24, first claim — `L` is effectively given.** The enumeration `Lenum` (indices
via `encodeList`/`decodeList`), Scott's two relations (`Lenum_interEq_computable`,
`Lenum_cons_computable`), the primitive-recursive intersection (`LenumInter`), and the master
index `0` (`Lenum_zero`) assemble into a `ComputablePresentation L`. -/
def Lpres : ComputablePresentation L where
  X := Lenum
  mem_X n := Lenum_mem n
  surj hY := Lenum_surj hY
  interEq_computable := Lenum_interEq_computable
  cons_computable := Lenum_cons_computable
  inter := LenumInter
  inter_primrec := primrec_LenumInter
  inter_spec h := LenumInter_spec h
  masterIdx := 0
  masterIdx_spec := Lenum_zero

open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

variable {β γ δ : Type*}

/-- The characteristic-function bundle needed to write down `funPresentation Lpres P` concretely:
`gN` for function-space consistency, `incl0`/`incl1` for `L`/`V`-inclusion, `eq1` for `V`-equality. -/
structure LFunData {V : NeighborhoodSystem β} (P : ComputablePresentation V) where
  gN : ℕ → ℕ
  incl0 : ℕ → ℕ
  incl1 : ℕ → ℕ
  eq1 : ℕ → ℕ
  hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf Lpres P (decodeList c))
    : Set (ApproximableMap L V)).Nonempty
  hgNp : Nat.Primrec gN
  hincl0 : ∀ s, incl0 s = 1 ↔ Lpres.X s.unpair.1 ⊆ Lpres.X s.unpair.2
  hincl0p : Nat.Primrec incl0
  hincl1 : ∀ s, incl1 s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2
  hincl1p : Nat.Primrec incl1
  heq1 : ∀ s, eq1 s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2
  heq1p : Nat.Primrec eq1

end DomainTheory.NeighbourhoodSystems.Exercise724
