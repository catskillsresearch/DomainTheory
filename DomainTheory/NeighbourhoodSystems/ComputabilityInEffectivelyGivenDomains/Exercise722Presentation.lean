/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.index
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_default
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysCanonicalCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysInterEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.IsPartiallyEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysPres
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat_zero_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool_encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBinDigit_of_natBool_some
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mapM_natBool_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_not_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_junk
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_pair_cat_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_pair_cap_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuelOkChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode_index
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_surj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_eq_denote_safe
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_inter_nonempty_iff_consistent
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_positivity
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive_inactive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.consistentB_sigma_safe
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.consistentB_safe_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_char_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_zero_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_char_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Ssys_cons_computable_of_primrec_ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_encodeListBool_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_sexprDepth_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_sexprGodelEncode_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool_eq_some_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mapM_natBool_eq_some
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool_eq_some
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_sound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_depth_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar_le_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive_exists_decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentBChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.primrec_ssysActiveChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.primrec_ssysConsistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentBChar_le_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_le_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_eq_ssysConsistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.primrec_ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Ssys_cons_computable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive_exists_decode

@[expose] public section

/-!
# Exercise 7.22 — computable presentation backbone (`SsysX`)

Enumeration `n ↦ SsysX n` for Scott's positive neighbourhood system `Ssys` (`Exercise722.lean`),
toward Definition 7.1 effective givenness. Indices decode to `SExpr` codes; non-empty denotations
are listed, while junk / empty-syntax indices map to the master neighbourhood `Σ` so every index
still names a member of `S` (`SsysX_mem`). Surjectivity onto `S` uses
`inS_iff_exists_denote` (`Exercise722Regular.lean`).

Sessions C9–C10 will add `RecDecidable₂` consistency and the `ComputablePresentation` structure;
relation (i) `interEq` remains deferred (see `Exercise722Decide.lean`, Session C7a).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-! ## Gödel codes for `SExpr` -/




























/-! ## The enumeration `SsysX` -/





/-! ## Definition 7.1 (ii) — recursively decidable consistency (Session C9)

Scott's consistency `∃ k, X_k ⊆ X_n ∩ X_m` on a positive system is equivalent to
`(X_n ∩ X_m).Nonempty` (`Ssys_isPositive`). On the `SsysX` enumeration, inactive indices
(decode failure / empty denotation → `SsysX = Σ`) make consistency automatic; active-active
pairs reduce to `consistentB` on decoded expressions. -/















/-! ### Session C9 — `RecDecidable₂` (primitive-recursive bridge)

The mathematics is finished (`ssys_cons_char_iff`). The generic packaging lemma is
`RecDecidable₂.of_paired_zero_one_char` in `Recursive.lean`: once a `{0,1}`-valued characteristic is
`Nat.Primrec`, `RecDecidable₂` follows immediately.

**Numeric characteristic** for the existing Bool decider (no new algorithm).

Unfolding `ssys_cons_char_iff` (which chains through `ssys_cons_iff` / `consistentB_iff`) can exceed
the default 200000 heartbeat budget; raise the limit for this section only. -/

set_option maxHeartbeats 5000000






/-! ### Session C9b7 — `ssysActiveChar`, `ssysConsistentBChar`

`Recursive.lean` cannot import this file (it would cycle: `Presentation → Definition71 →
Recursive`), so its C9b5/C9b6 Gödel mirror (`c9b5_sexprGodelEncode`/`c9b5_sexprDepth`) is a
self-contained *structural* copy of `SExpr.encode`/`sexprDepth` above, not literally the same
function. The bridge equalities below (provable here, downstream, where both sides are visible)
let every C9b5/C9b6 correctness theorem be re-applied against the *real* `SExpr.encode`/
`sexprDepth`/`denote`, without re-deriving any of their induction. -/

theorem c9b5_boolNat_eq (b : Bool) : Domain.Recursive.c9b5_boolNat b = boolNat b := by
  cases b <;> rfl




/-! #### Decode soundness: `decodeFuel` recovers exactly the canonical encoding, within fuel

Needed to instantiate C9b5/C9b6's `_eq_one_iff` theorems (stated at `c9b5_sexprGodelEncode e` /
`c9b5_sexprDepth e ≤ fuel`) against a code `n.unpair.1` that merely *decodes* to some `e` under
`SExpr.decode` — not one already known to equal `SExpr.encode e` syntactically. -/












/-! ### Session C9b8 — closing the `C9b` umbrella

`decodeFuelOkChar`/`autStateCardFuelChar`/`matchesBChar`/`decideNonemptyBChar`/`consistentBChar`
are jointly primitive recursive in `(fuel, code)` (see `Recursive.lean`'s course-of-values
sections), so `ssysActiveChar`/`ssysConsistentBChar` compose directly, with no further new
infrastructure needed here. -/








/-! ### Session C7b — `ssysInterEqChar` (Exercise 7.22k)

Definition 7.1 relation (i) — `SsysX n ∩ SsysX m = SsysX k` — via the `Exercise722Equiv.lean` /
`Recursive.lean` language-equivalence decider `interEqChar`. `safeDecodeActive` already gives a
uniform canonical `SExpr` representative for every index (junk/inactive ↦ `.sigma`,
`SsysX_eq_denote_safe`), so unlike `ssysConsistentBChar` (where inactive indices are *trivially*
consistent with anything, since `Σ` is the top element) there is no active/inactive case split
here: equality is genuinely about the canonical representative in every case. -/


theorem ssysCanonicalCode_eq (n : ℕ) : ssysCanonicalCode n = SExpr.encode (safeDecodeActive n) := by
  unfold ssysCanonicalCode
  by_cases hn : ssysActive n = true
  · rw [(ssysActiveChar_eq_one_iff n).mpr hn, Domain.Recursive.selectFn_one]
    obtain ⟨e, hdec⟩ := ssysActive_exists_decode hn
    have hac : n.unpair.1 = SExpr.encode e := decodeFuel_sound hdec
    rw [hac]
    congr 1
    unfold safeDecodeActive
    rw [hdec]
    have : decideNonemptyB e = true := by
      unfold ssysActive at hn; rw [hdec] at hn; exact hn
    simp [this]
  · have hn0 : ssysActiveChar n = 0 := by
      have hle := ssysActiveChar_le_one n
      have hne : ssysActiveChar n ≠ 1 := fun h => hn ((ssysActiveChar_eq_one_iff n).mp h)
      omega
    have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    rw [hn0, Domain.Recursive.selectFn_zero, safeDecodeActive_inactive n hnf]

theorem sexprDepth_safeDecodeActive_le (n : ℕ) : sexprDepth (safeDecodeActive n) ≤ n.unpair.2 + 1 := by
  by_cases hn : ssysActive n = true
  · obtain ⟨e, hdec⟩ := ssysActive_exists_decode hn
    have hda : sexprDepth e ≤ n.unpair.2 + 1 := decodeFuel_depth_le hdec
    have heq : safeDecodeActive n = e := by
      unfold safeDecodeActive
      rw [hdec]
      have : decideNonemptyB e = true := by
        unfold ssysActive at hn; rw [hdec] at hn; exact hn
      simp [this]
    rw [heq]; exact hda
  · have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    rw [safeDecodeActive_inactive n hnf]
    simp [sexprDepth]

theorem ssys_interEq_iff (n m k : ℕ) :
    SsysX n ∩ SsysX m = SsysX k ↔
      denote (.cap (safeDecodeActive n) (safeDecodeActive m)) = denote (safeDecodeActive k) := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, SsysX_eq_denote_safe, denote_cap]


theorem ssysInterEqChar_le_one (t : ℕ) : ssysInterEqChar t ≤ 1 := by
  unfold ssysInterEqChar
  exact Domain.Recursive.interEqChar_le_one _ _ _

theorem ssysInterEqChar_eq_one_iff (n m k : ℕ) :
    ssysInterEqChar (Nat.pair n (Nat.pair m k)) = 1 ↔ SsysX n ∩ SsysX m = SsysX k := by
  unfold ssysInterEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [ssys_interEq_iff]
  have hfuel : n.unpair.2 + m.unpair.2 + k.unpair.2 + 3 ≥
      c9b5_sexprDepth (.cap (safeDecodeActive n) (safeDecodeActive m)) ∧
      n.unpair.2 + m.unpair.2 + k.unpair.2 + 3 ≥ c9b5_sexprDepth (safeDecodeActive k) := by
    rw [c9b5_sexprDepth_eq, c9b5_sexprDepth_eq]
    have hn := sexprDepth_safeDecodeActive_le n
    have hm := sexprDepth_safeDecodeActive_le m
    have hk := sexprDepth_safeDecodeActive_le k
    simp only [sexprDepth]
    omega
  rw [show Domain.Recursive.capCode (ssysCanonicalCode n) (ssysCanonicalCode m) =
      c9b5_sexprGodelEncode (.cap (safeDecodeActive n) (safeDecodeActive m)) from ?_,
    show ssysCanonicalCode k = c9b5_sexprGodelEncode (safeDecodeActive k) from ?_,
    Domain.Recursive.interEqChar_eq_one_iff hfuel.1 hfuel.2]
  · rw [c9b5_sexprGodelEncode_eq]; exact ssysCanonicalCode_eq k
  · unfold Domain.Recursive.capCode
    rw [ssysCanonicalCode_eq, ssysCanonicalCode_eq, ← c9b5_sexprGodelEncode_eq,
      ← c9b5_sexprGodelEncode_eq]
    rfl

theorem primrec_ssysInterEqChar : Nat.Primrec ssysInterEqChar := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcanon : Nat.Primrec (fun n : ℕ => ssysCanonicalCode n) := by
    have := primrec_ssysActiveChar
    refine (Domain.Recursive.primrec_selectFn this Nat.Primrec.left
      (Nat.Primrec.const (SExpr.encode .sigma))).of_eq fun n => ?_
    unfold ssysCanonicalCode; rfl
  have hcn : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.1) := hcanon.comp hn
  have hcm : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.2.unpair.1) := hcanon.comp hm
  have hck : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.2.unpair.2) := hcanon.comp hk
  have hfuel : Nat.Primrec (fun t : ℕ =>
      t.unpair.1.unpair.2 + t.unpair.2.unpair.1.unpair.2 + t.unpair.2.unpair.2.unpair.2 + 3) :=
    Domain.Recursive.primrec_add₂
      (Domain.Recursive.primrec_add₂
        (Domain.Recursive.primrec_add₂
          (Nat.Primrec.right.comp hn) (Nat.Primrec.right.comp hm))
        (Nat.Primrec.right.comp hk))
      (Nat.Primrec.const 3)
  have hcap : Nat.Primrec (fun t : ℕ =>
      Domain.Recursive.capCode (ssysCanonicalCode t.unpair.1)
        (ssysCanonicalCode t.unpair.2.unpair.1)) := by
    have hp : Nat.Primrec (fun t : ℕ => Nat.pair 3 (Nat.pair (ssysCanonicalCode t.unpair.1)
        (ssysCanonicalCode t.unpair.2.unpair.1))) :=
      Nat.Primrec.pair (Nat.Primrec.const 3) (Nat.Primrec.pair hcn hcm)
    refine hp.of_eq fun t => ?_
    unfold Domain.Recursive.capCode; rfl
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair
      (t.unpair.1.unpair.2 + t.unpair.2.unpair.1.unpair.2 + t.unpair.2.unpair.2.unpair.2 + 3)
      (Nat.pair (Domain.Recursive.capCode (ssysCanonicalCode t.unpair.1)
          (ssysCanonicalCode t.unpair.2.unpair.1))
        (ssysCanonicalCode t.unpair.2.unpair.2))) :=
    Nat.Primrec.pair hfuel (Nat.Primrec.pair hcap hck)
  refine (Domain.Recursive.primrec_interEqChar.comp hpack).of_eq fun t => ?_
  unfold ssysInterEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Exercise 7.22k.** Definition 7.1 relation (i) is recursively decidable for `Ssys`. -/
theorem Ssys_interEq_computable :
    RecDecidable₃ (fun n m k => SsysX n ∩ SsysX m = SsysX k) :=
  RecDecidable₃.of_triple_zero_one_char primrec_ssysInterEqChar
    (fun t => by
      rcases (show ssysInterEqChar t = 0 ∨ ssysInterEqChar t = 1 from by
        have := ssysInterEqChar_le_one t; omega) with h | h <;> simp [h])
    (fun n m k => (ssysInterEqChar_eq_one_iff n m k).symm)

/-! ### Session C10 — Definition 7.1 packaging for `Ssys` (Exercise 7.22j)

**Historical note (superseded by C7b / 7.22k, kept for the record).** At the time this session ran,
relation (i) — `Xₙ ∩ Xₘ = X_k`, i.e. whether two *different* syntactic caps denote the *same*
language — was open: strictly harder than emptiness/consistency, since the fragment
`{sigma, single, cat, cap}` is not closed under complement, so `consistentB`/`decideNonemptyB`
(which only ever test emptiness) cannot expose language inequality (concrete obstruction:
`sigma_ne_containsZero`, see `Exercise722Decide.lean`). So `Ssys` got a **partial** presentation
carrying only what was proved then: the enumeration onto `S` (`SsysX`/`SsysX_mem`/`SsysX_surj`)
plus relation (ii) (`Ssys_cons_computable`).

**Session C7b since closed relation (i)** (`Ssys_interEq_computable`, below) via a choice-free
`Finset`-subset-construction automaton simulation (`Exercise722Equiv.lean`) — so `Ssys` now
satisfies **all of Definition 7.1 exactly as Scott states it** (enumeration, plus both relations
recursively decidable), between `SsysPres`/`Ssys_partially_effectively_given` here and
`Ssys_interEq_computable` in the C7b section. What is *not* provided is an instance of this
codebase's stronger `ComputablePresentation` (`Definition71.lean`) — used throughout the rest of
Lecture VII's formalisation (Theorem 7.4–7.6, Exercise 7.13–7.18, Proposition 7.7/7.10) — which
additionally carries a primitive-recursive intersection witness `inter`/`inter_primrec`/
`inter_spec` and a `masterIdx`. Those two fields are not part of Definition 7.1's text and are not
asked for by Exercise 7.22; completing them would be mechanical (7.22k's `ssysCanonicalCode`/
`capCode` already compute the right index) and is worth doing only if a later exercise wants to
feed `Ssys` into that shared apparatus. -/




/-- **Exercise 7.22j.** `Ssys` — Scott's positive system generated by singleton languages under
concatenation and consistent intersection — is partially effectively given: Definition 7.1
relation (ii) is recursively decidable (`Ssys_cons_computable`, closing C9 / **7.22i(b)**).

The name "partially" now undersells the full picture: relation (i) is *also* proven, separately,
as `Ssys_interEq_computable` (Exercise 7.22k, `ConsistencyPresentation` was never extended with an
`interEq_computable` field to absorb it). Together, `SsysPres` and `Ssys_interEq_computable` show
`Ssys` satisfies Definition 7.1 **exactly as Scott states it** — enumeration, plus both relations
recursively decidable — with nothing deferred. What remains unbuilt is only this codebase's
*stronger* `ComputablePresentation` (`Definition71.lean`), which the rest of Lecture VII's
formalisation relies on but which is not part of Definition 7.1's text; see the section docstring
above. -/
theorem Ssys_partially_effectively_given : IsPartiallyEffectivelyGiven Ssys := ⟨SsysPres⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
