/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality

/-!
# Scott 1976, §3 — enumeration, degrees, and the semigroup of operators

Theorems 3.1–3.7.
-/

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Packed 5-tuple of the remaining combinators of Theorem 2.4. -/
def Gpack : Pomega :=
  seq2 sucC (seq2 predC (seq2 condC (seq2 Kcomb Scomb)))

/-- **Scott 1976, (3.3).** `G = cond(⟨suc, pred, cond, K, S⟩)(0)`. -/
def Gcomb : Pomega :=
  graph (fun z => condSet z Gpack zeroC)

theorem Gcomb_app (z : Pomega) :
    funOf Gcomb z = condSet z Gpack zeroC :=
  beta (condSet_isScottContinuous_left Gpack zeroC) z

theorem Gcomb_zero : funOf Gcomb (ofNat 0) = Gpack := by
  rw [Gcomb_app, eq_2_7_zero]

/-- `0 ∉ G`, so `G` is a positive non-zero test. -/
theorem not_mem_zero_Gcomb : 0 ∉ Gcomb := by
  intro h
  rcases h with ⟨n, m, hm, hmem⟩
  have hnm : n = 0 ∧ m = 0 := by
    have : pair n m = 0 := hm.symm
    have : pair n m = pair 0 0 := by simpa [pair_zero_zero] using this
    exact pair_inj this
  rcases hnm with ⟨rfl, rfl⟩
  simp [e_zero, condSet] at hmem

theorem Gpack_ne_bot : Gpack ≠ botElem := by
  intro h
  have hs : sucC = funOf botElem (ofNat 0) := by
    have := congrArg (fun w => funOf w (ofNat 0)) h
    simpa [Gpack, seq2_app_zero] using this
  have h1 : (1 : ℕ) ∈ funOf sucC (ofNat 0) := by
    rw [sucC_app]; exact ⟨0, rfl, rfl⟩
  rw [hs] at h1
  simp [funOf, botElem] at h1

/-- **Scott 1976, (3.8).** `G(G) = 0`. -/
theorem Gcomb_app_self : funOf Gcomb Gcomb = zeroC := by
  have hne : Gcomb ≠ botElem := by
    intro h
    have : Gpack = funOf botElem (ofNat 0) := by
      have := congrArg (fun w => funOf w (ofNat 0)) h
      simpa [Gcomb_zero] using this
    have hbot : funOf botElem (ofNat 0) = botElem := by
      ext; simp [funOf, botElem]
    exact Gpack_ne_bot (this.trans hbot)
  rw [Gcomb_app]
  exact eq_2_7_pos Gpack zeroC Gcomb not_mem_zero_Gcomb hne

theorem Gpack_zero : funOf Gpack (ofNat 0) = sucC := by
  simp [Gpack, seq2_app_zero]

theorem Gpack_one : funOf Gpack (ofNat 1) =
    seq2 predC (seq2 condC (seq2 Kcomb Scomb)) := by
  simp [Gpack, seq2_app_one]

/-- The six constants are recovered from `G` and `0` by projection. -/
theorem sucC_from_G : sucC = funOf (funOf Gcomb zeroC) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_zero]

theorem predC_from_G :
    predC = funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_zero]

theorem condC_from_G :
    condC =
      funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_zero]

theorem Kcomb_from_G :
    Kcomb =
      funOf (funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        (ofNat 1)) zeroC := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_one, seq2_app_zero]

theorem Scomb_from_G :
    Scomb =
      funOf (funOf (funOf (funOf (funOf Gcomb zeroC) (ofNat 1)) (ofNat 1))
        (ofNat 1)) (ofNat 1) := by
  have : zeroC = ofNat 0 := rfl
  simp [this, Gcomb_zero, Gpack_one, seq2_app_one, seq2_app_one, seq2_app_one]

theorem bot_combinatory : IsCombinatory botElem :=
  (show funOf predC zeroC = botElem by rw [predC_app]; exact eq_2_6) ▸
    IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

/-- `seq2 x y` is the combinator `S (S (K (cond x)) (S (K (cond y ⊥)) pred)) I`. -/
theorem seq2_eq_SK (x y : Pomega) :
    seq2 x y =
      funOf (funOf Scomb
          (funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
            (funOf (funOf Scomb
                (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
              predC)))
        (funOf (funOf Scomb Kcomb) Kcomb) := by
  have hinter :
      funOf (funOf Scomb
          (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
        predC =
      graph (fun z => condSet (predSet z) y botElem) := by
    rw [Scomb_beta2]
    apply congrArg graph
    funext z
    rw [Kcomb_beta2, predC_app, predC_app]
    have : zeroC = ofNat 0 := rfl
    rw [this, eq_2_6, condC_beta3]
  have hF :
      funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
        (funOf (funOf Scomb
            (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
          predC) =
      graph (fun z =>
        funOf (funOf condC x) (condSet (predSet z) y botElem)) := by
    rw [Scomb_beta2, hinter]
    apply congrArg graph
    funext z
    rw [Kcomb_beta2]
    apply congrArg (funOf (funOf condC x))
    exact beta (theorem_1_3 (condSet_isScottContinuous_left y botElem)
      predSet_isScottContinuous) z
  rw [Scomb_beta2, hF, SKK_eq_I]
  apply congrArg graph
  funext z
  have hz : funOf (graph (fun x => x)) z = z := beta id_isScottContinuous z
  rw [hz]
  have hβ : funOf (graph (fun z =>
      funOf (funOf condC x) (condSet (predSet z) y botElem))) z =
      funOf (funOf condC x) (condSet (predSet z) y botElem) :=
    beta (theorem_1_3 (funOf_isScottContinuous (funOf condC x))
      (theorem_1_3 (condSet_isScottContinuous_left y botElem)
        predSet_isScottContinuous)) z
  rw [hβ, condC_beta3]

theorem seq2_combinatory {x y : Pomega}
    (hx : IsCombinatory x) (hy : IsCombinatory y) :
    IsCombinatory (seq2 x y) := by
  have hyb : IsCombinatory (funOf (funOf condC y) (funOf predC zeroC)) :=
    .app (.app .cond hy) (.app .pred .zero)
  have hinter : IsCombinatory
      (funOf (funOf Scomb (funOf Kcomb
          (funOf (funOf condC y) (funOf predC zeroC)))) predC) :=
    .app (.app .S (.app .K hyb)) .pred
  have hF : IsCombinatory
      (funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
        (funOf (funOf Scomb
            (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
          predC)) :=
    .app (.app .S (.app .K (.app .cond hx))) hinter
  have hI : IsCombinatory (funOf (funOf Scomb Kcomb) Kcomb) :=
    .app (.app .S .K) .K
  have h := IsCombinatory.app (IsCombinatory.app IsCombinatory.S hF) hI
  simpa [seq2_eq_SK x y] using h

theorem Gpack_combinatory : IsCombinatory Gpack :=
  seq2_combinatory .suc
    (seq2_combinatory .pred
      (seq2_combinatory .cond (seq2_combinatory .K .S)))

theorem Gcomb_eq_condC : Gcomb = funOf (funOf condC Gpack) zeroC :=
  (condC_beta2 Gpack zeroC).symm

theorem Gcomb_combinatory : IsCombinatory Gcomb := by
  simpa [Gcomb_eq_condC] using
    IsCombinatory.app (IsCombinatory.app IsCombinatory.cond Gpack_combinatory)
      IsCombinatory.zero

/-- Generation from Scott's single generator `G` (since `G(G) = 0`). -/
inductive GeneratedFromG : Pomega → Prop
  | G : GeneratedFromG Gcomb
  | app {u v} : GeneratedFromG u → GeneratedFromG v →
      GeneratedFromG (funOf u v)

/-- **Scott 1976, Theorem 3.1 (The generator theorem).**
All LAMBDA-definable elements are obtained from `G` by iterated application. -/
theorem sucC_zero : funOf sucC zeroC = ofNat 1 := by
  rw [sucC_app]
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    simp [zeroC, ofNat] at hn
    subst hn
    simpa [ofNat] using hk
  · intro hk
    simp [ofNat] at hk
    exact ⟨0, rfl, hk⟩

theorem theorem_3_1 {u : Pomega} :
    IsCombinatory u ↔ GeneratedFromG u := by
  have hzero : GeneratedFromG zeroC := by
    simpa [Gcomb_app_self] using
      GeneratedFromG.app GeneratedFromG.G GeneratedFromG.G
  constructor
  · intro hu
    have hsuc : GeneratedFromG sucC := by
      simpa [sucC_from_G] using
        GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hzero
    have hone : GeneratedFromG (ofNat 1) := by
      simpa [sucC_zero] using GeneratedFromG.app hsuc hzero
    induction hu with
    | zero => exact hzero
    | suc => exact hsuc
    | pred =>
      simpa [predC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone) hzero
    | cond =>
      simpa [condC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone) hone)
          hzero
    | K =>
      simpa [Kcomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone)
                hone)
            hone)
          hzero
    | S =>
      simpa [Scomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone)
                hone)
            hone)
          hone
    | app _ _ iu iv => exact .app iu iv
  · intro hu
    induction hu with
    | G => exact Gcomb_combinatory
    | app _ _ iu iv => exact .app iu iv

/-- **Scott 1976, (3.4).** `apply(n)(m) = (n, m) + 1`. -/
def applyNat (n m : ℕ) : ℕ := pair n m + 1

/-- The application selected by one positive Gödel code. -/
def valStepValue (v : Pomega) : ℕ → Pomega
  | 0 => botElem
  | p + 1 =>
      funOf (funOf v (ofNat (unpair p).1))
        (funOf v (ofNat (unpair p).2))

/-- **Scott 1976, (3.7).** One step of the enumerator.  The positive
branch is written as `minExtend`; this is extensionally Scott's existential
clause and exposes its continuity. -/
def valStep (v : Pomega) : Pomega :=
  graph (fun k => condSet k Gcomb (minExtend (valStepValue v) k))

def valC : Pomega := fix valStep

/-- The r.e. / LAMBDA-definable closed elements. -/
def RE : Set Pomega := {u | IsCombinatory u}

/-- **Scott 1976, (3.5)–(3.6).** Components of a pair code. -/
noncomputable def opNat (k : ℕ) : ℕ := (unpair k).1
noncomputable def argNat (k : ℕ) : ℕ := (unpair k).2

/-- **Scott 1976, (3.7) / Theorem 3.2.** `val(0) = G` and
`val(apply(n)(m)) = val(n)(val(m))`. -/
noncomputable def valNat : ℕ → Pomega :=
  Nat.strongRec fun n rec =>
    match n with
    | 0 => Gcomb
    | n + 1 =>
        rec (unpair n).1
          (Nat.lt_of_lt_of_eq
            (pair_lt_left (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n))) ⬝
        rec (unpair n).2
          (Nat.lt_of_lt_of_eq
            (pair_lt_right (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n)))

/-- **Scott 1976, Theorem 3.2 (i).** `val(0) = G`. -/
theorem valNat_zero : valNat 0 = Gcomb := by
  unfold valNat
  rw [Nat.strongRec]

theorem valNat_succ (n : ℕ) :
    valNat (n + 1) = valNat (unpair n).1 ⬝ valNat (unpair n).2 := by
  unfold valNat
  rw [Nat.strongRec]

/-- **Scott 1976, Theorem 3.2 (ii).** `val(apply(n)(m)) = val n (val m)`. -/
theorem valNat_apply (n m : ℕ) :
    valNat (applyNat n m) = valNat n ⬝ valNat m := by
  rw [applyNat, valNat_succ, unpair_pair]

/-- A stage by which the finite application tree coded by `n` has appeared
in the least-fixed-point construction of `valC`. -/
noncomputable def valRank : ℕ → ℕ
  | 0 => 1
  | p + 1 => max (valRank (unpair p).1) (valRank (unpair p).2) + 1
decreasing_by
  · exact (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)
  · exact (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)

/-- Every combinatory element appears in Scott's enumeration. -/
theorem theorem_3_2_surjective {u : Pomega} (hu : IsCombinatory u) :
    ∃ n, valNat n = u := by
  revert hu
  rw [theorem_3_1]
  intro h
  induction h with
  | G => exact ⟨0, valNat_zero⟩
  | app _ _ iu iv =>
    obtain ⟨n, hn⟩ := iu
    obtain ⟨m, hm⟩ := iv
    exact ⟨applyNat n m, by rw [valNat_apply, hn, hm]⟩

/-- **Scott 1976, (3.11).** `num(0) = 1`, `num(n+1) = apply(12, num n)`. -/
def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)

theorem primrec_applyNat : Primrec₂ applyNat :=
  (Primrec.succ.comp primrec_pair).of_eq fun _ => rfl

theorem primrec_num : Primrec num :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (1 : ℕ))
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => applyNat 12 p.2)
    Primrec.id (Primrec.const 1)
    (show Primrec fun q : ℕ × ℕ × ℕ => applyNat 12 q.2.2 from
      primrec_applyNat.comp (Primrec.const 12) (Primrec.snd.comp Primrec.snd))).of_eq
    fun n => by
      induction n with
      | zero => rfl
      | succ n ih =>
        change applyNat 12 (Nat.rec 1 (fun n IH => applyNat 12 (n, IH).2) n) =
          applyNat 12 (num n)
        have ih' : Nat.rec 1 (fun n IH => applyNat 12 (n, IH).2) n = num n := by
          simpa [id] using ih
        rw [ih']

/-- **Scott 1976, Theorem 3.3 (i).** The set denoted by the code `v(n)`. -/
def secondRecVal (u : Pomega) : Pomega :=
  graph (fun x => ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))))

/-- The primitive-recursive numerical substitution used in Theorem 3.3. -/
def secondRecSubst (m : ℕ) : ℕ := applyNat m (num m)

theorem primrec_secondRecSubst : Primrec secondRecSubst :=
  primrec_applyNat.comp Primrec.id primrec_num

/-- A fixed combinator realizing `m ↦ apply(m)(num(m))`. -/
noncomputable def secondRecSubstC : Pomega :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose

theorem secondRecSubstC_combinatory : IsCombinatory secondRecSubstC :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.1

/-- The uniform operator `u ↦ λm∈ω. u(apply(m)(num(m)))`. -/
def secondRecOperator : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb
      (funOf (funOf Scomb (funOf Kcomb Scomb)) Kcomb))
      (funOf Kcomb secondRecSubstC))

theorem secondRecOperator_combinatory : IsCombinatory secondRecOperator :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app
      (.app .S (.app (.app .S (.app .K .S)) .K))
      (.app .K secondRecSubstC_combinatory))

/-- A Gödel code for the uniform operator in Theorem 3.3. -/
noncomputable def secondRecOperatorCode : ℕ :=
  (theorem_3_2_surjective secondRecOperator_combinatory).choose

/-- Scott's primitive-recursive function `v` in Theorem 3.3. -/
noncomputable def secondRecV (n : ℕ) : ℕ :=
  applyNat secondRecOperatorCode n

/-- **Scott 1976, Theorem 3.3 (ii).** `rec(n) = apply(v(n))(num(v(n)))`. -/
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

/-- A Gödel number of `Y`, used for a Kleene-style fixed point on codes. -/
noncomputable def Ycode : ℕ :=
  (theorem_3_2_surjective Ycomb_combinatory).choose

/-- **Scott 1976, Theorem 3.3 (iii).** `val(rec(n)) = val(n)(rec(n))`
via `Y` (the paper's `v`/`num` packaging is `recNat`). -/
noncomputable def recCode (n : ℕ) : ℕ := applyNat Ycode n

/-- A closed LAMBDA term for the body defining binary intersection. -/
def interStepTerm : Term :=
  let omega : Term := .lam 4 (.app (.var 4) (.var 4))
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 1)
      (.cond (.var 2) .zero (.app omega omega))
      (.succ (.app (.app (.var 0) (.pred (.var 1))) (.pred (.var 2)))))))

theorem interStepTerm_interp :
    interp interStepTerm (fun _ => botElem) = graph interStep := by
  unfold interStepTerm interStep
  simp only [interp, envSet, Function.update_self]
  apply congrArg graph
  funext f
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  congr 2
  exact eq_2_14

theorem interC_combinatory : IsCombinatory interC := by
  have hbody : IsCombinatory (graph interStep) := by
    rw [← interStepTerm_interp]
    exact theorem_2_4_closed interStepTerm
  have hfix := IsCombinatory.app Ycomb_combinatory hbody
  rw [theorem_2_5 interStep_isScottContinuous] at hfix
  exact hfix

noncomputable def interCode : ℕ :=
  (theorem_3_2_surjective interC_combinatory).choose

/-- The primitive-recursive diagonal intersection code used in Theorem 3.4. -/
noncomputable def diagonalInterCode (n : ℕ) : ℕ :=
  applyNat (applyNat interCode (num n)) n

def unionBits : List ℕ → Pomega
  | [] => botElem
  | k :: ks => ofNat k ∪ unionBits ks

def bitList (j : ℕ) : List ℕ :=
  (List.range (j + 1)).filter (fun k => j.testBit k)

/-- A closed term for binary union.  Keeping this term explicit avoids making
`fin` choose a fresh code separately for every finite set. -/
def unionTerm : Term :=
  .lam 0 (.lam 1 (.cond (.lam 2 .zero) (.var 0) (.var 1)))

theorem unionTerm_interp :
    interp unionTerm (fun _ => botElem) =
      graph (fun x => graph (fun y => x ∪ y)) := by
  unfold unionTerm
  simp only [interp, envSet, Function.update_self]
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  change condSet (graph fun _ => zeroC) x y = x ∪ y
  simpa [condC_beta3, Kcomb_beta] using union_via_cond x y

theorem unionOperator_combinatory :
    IsCombinatory (graph (fun x => graph (fun y => x ∪ y))) := by
  rw [← unionTerm_interp]
  exact theorem_2_4_closed unionTerm

/-- One fixed Gödel code for the binary union operator. -/
noncomputable def unionCode : ℕ :=
  (theorem_3_2_surjective unionOperator_combinatory).choose

noncomputable def botCode : ℕ :=
  (theorem_3_2_surjective bot_combinatory).choose

/-- Primitive recursion scanning the first `k` bits of `j`. -/
noncomputable def finAux (j : ℕ) : ℕ → ℕ
  | 0 => botCode
  | k + 1 =>
      if j.testBit k then
        applyNat (applyNat unionCode (num k)) (finAux j k)
      else finAux j k

/-- **Scott 1976, before Theorem 3.5.** A uniform primitive-recursive code
for `e j`; unlike the former definition, this makes only one fixed choice,
namely a code for binary union. -/
noncomputable def fin (j : ℕ) : ℕ := finAux j (j + 1)

/-- Appendix `q` of Theorem 3.5: `q = {(j,m) | m ∈ val(p(fin j))}`. -/
def myhillQ (val : ℕ → Pomega) (p : ℕ → ℕ) : Pomega :=
  {k | ∃ j m, k = pair j m ∧ m ∈ val (p (fin j))}

/-- **Scott 1976, before Theorem 3.5.** Extensionality of a Gödel-number map. -/
def IsExtensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n m, val n = val m → val (p n) = val (p m)

def myhillRealizer (p : ℕ → ℕ) : Pomega → Pomega :=
  funOf (myhillQ valNat p)

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem exists_triangle_succ (k : ℕ) : ∃ w, k < triangle (w + 1) :=
  ⟨k, by
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩

/-- Computable inverse of Scott pairing, equal to `unpair`. -/
def unpairComp (k : ℕ) : ℕ × ℕ :=
  let w := Nat.find (exists_triangle_succ k)
  let m := k - triangle w
  (w - m, m)

/-- Finite derivation that `member ∈ valNat code`, with the application
witness `t` stored on positive codes. -/
abbrev ValTrace := List (ℕ × ℕ × ℕ)

def valTraceHas (tr : ValTrace) (code member : ℕ) : Prop :=
  ∃ t, (code, member, t) ∈ tr

def valEntryJustified (tr : ValTrace) (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 = 0 ∨
    (valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) ∧
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i)

def valTraceStruct (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, valEntryJustified tr e

def valTraceG (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, e.1 = 0 → e.2.1 ∈ Gcomb

def valTraceOk (tr : ValTrace) : Prop :=
  valTraceStruct tr ∧ valTraceG tr

/-- Bounded scan for the least `w` with `k < triangle (w+1)`. -/
def unpairWRec (k n : ℕ) : ℕ :=
  Nat.rec 0 (fun w ih => if k < triangle (w + 1) then ih else w + 1) n

/-- Least `w` with `k < triangle (w+1)`, computed by bounded recursion. -/
def unpairW (k : ℕ) : ℕ := unpairWRec k k

noncomputable def condCode : ℕ :=
  (theorem_3_2_surjective IsCombinatory.cond).choose

/-- Appendix case 2: `u(m)` with `val(u m) = e_j ∪ (val m ⊃ val n, val n)`. -/
noncomputable def myhillCase2Code (j n m : ℕ) : ℕ :=
  applyNat (applyNat unionCode (fin j))
    (applyNat (applyNat (applyNat condCode n) n) m)

/-- Shifted enumerator of the halting set: `0` is the miss marker. -/
def haltEnum (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome
    then t.unpair.1 + 1 else 0

theorem primrec_haltEnum : Primrec haltEnum := by
  have heval : Primrec fun t : ℕ =>
      evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0 :=
    primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.unpair)
          ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.const 0)
  exact (Primrec.cond (Primrec.option_isSome.comp heval)
    (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.const 0)).of_eq fun t => by
    simp [haltEnum]

def beforeHalt (m j : ℕ) : Prop := ∀ i < j + 1, haltEnum i ≠ m

instance : DecidableRel beforeHalt :=
  fun m j => decidable_of_iff (∀ i : Fin (j + 1), haltEnum i.val ≠ m)
    ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.val i.isLt⟩

theorem primrecPred_beforeHalt : PrimrecRel beforeHalt := by
  have hne : PrimrecRel fun (i m : ℕ) => haltEnum i ≠ m :=
    (Primrec.eq.comp (primrec_haltEnum.comp Primrec.fst) Primrec.snd).not
  exact (hne.forall_mem_list.comp (Primrec.list_range.comp
      (Primrec.succ.comp Primrec.snd)) Primrec.fst).of_eq fun _ => by
    simp [beforeHalt]

def filterNum (q : ℕ) : ℕ :=
  if beforeHalt q.unpair.1 q.unpair.2 then q.unpair.2 + 1 else 0

theorem primrec_filterNum : Nat.Primrec filterNum := by
  have h : Primrec filterNum :=
    (Primrec.ite (c := fun q : ℕ => beforeHalt q.unpair.1 q.unpair.2)
      (primrecPred_beforeHalt.comp
        (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 0)).of_eq fun q => by
      simp [filterNum]
  exact Primrec.nat_iff.mp h

noncomputable def filterRealizer : Pomega :=
  (primrec_realized primrec_filterNum).choose

theorem filterRealizer_combinatory : IsCombinatory filterRealizer :=
  (primrec_realized primrec_filterNum).choose_spec.1

def filterEnv : ℕ → Pomega
  | 3 => filterRealizer
  | 4 => pairComb
  | 5 => dollarC
  | 6 => predC
  | 7 => topElem
  | _ => botElem

theorem filterEnv_combinatory : ∀ i, IsCombinatory (filterEnv i)
  | 3 => filterRealizer_combinatory
  | 4 => pairComb_combinatory
  | 5 => dollarC_combinatory
  | 6 => .pred
  | 7 => topElem_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 8 => botElem_combinatory

/-- `λm. pred($ (λj. filterRealizer(pair m j)) ⊤)`. -/
def filterTerm : Term :=
  .lam 0 (.pred
    (.app (.app (.var 5)
      (.lam 1 (.app (.var 3) (.app (.app (.var 4) (.var 0)) (.var 1)))))
      (.var 7)))

def filterC : Pomega := interp filterTerm filterEnv

theorem filterC_combinatory : IsCombinatory filterC := by
  rw [filterC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ filterEnv_combinatory

noncomputable def filterOp : ℕ :=
  (theorem_3_2_surjective filterC_combinatory).choose

noncomputable def myhillFilterCode (m : ℕ) : ℕ := applyNat filterOp (num m)

noncomputable def myhillCase1Code (n m : ℕ) : ℕ :=
  applyNat (applyNat interCode n) (myhillFilterCode m)

/-- **Scott 1976, Definition.** Enumeration degree of `a`. -/
def Deg (a : Pomega) : Set Pomega :=
  {u | ∃ r, IsCombinatory r ∧ u = funOf r a}

/-- Combinatory subalgebra: contains `G` and is closed under application. -/
def IsSubalgebra (A : Set Pomega) : Prop :=
  Gcomb ∈ A ∧ ∀ ⦃u v⦄, u ∈ A → v ∈ A → funOf u v ∈ A

def Icomb_SK : Pomega := funOf (funOf Scomb Kcomb) Kcomb

/-- The paper's single generator of a finite tuple: `cond(⟨xs⟩)(G)`. -/
def packList : List Pomega → Pomega
  | [] => botElem
  | x :: xs => seq2 x (packList xs)

def singleGenerator (xs : List Pomega) : Pomega :=
  funOf (funOf condC (packList xs)) Gcomb

/-- **Scott 1976, (3.13)–(3.14).** Semigroup generators. -/
def Rcomb : Pomega := graph (fun x => seq2 (ofNat 0) x)

def Lcomb : Pomega :=
  graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)))

/-- **Scott 1976, (3.15).** Positive branch of `ū`: `⟨1, u, x₁⟩`. -/
def barPos (u x : Pomega) : Pomega :=
  seqCons (ofNat 1) (seq2 u (funOf x (ofNat 1)))

/-- A closed divergent term denoting bottom. -/
def enumBottomTerm : Term :=
  .app (.lam 9 (.app (.var 9) (.var 9)))
    (.lam 9 (.app (.var 9) (.var 9)))

/-- `t` does not depend on environment slot `i`. -/
def Term.Avoids (i : ℕ) : Term → Prop
  | .var j => j ≠ i
  | .zero => True
  | .succ t => t.Avoids i
  | .pred t => t.Avoids i
  | .cond z x y => z.Avoids i ∧ x.Avoids i ∧ y.Avoids i
  | .app u x => u.Avoids i ∧ x.Avoids i
  | .lam j body => j = i ∨ body.Avoids i

/-- Term-level binary sequence constructor. -/
def seq2Term (a b : Term) : Term :=
  .lam 8 (.cond (.var 8) a
    (.cond (.pred (.var 8)) b enumBottomTerm))

/-- Term-level sequence cons constructor. -/
def seqConsTerm (a xs : Term) : Term :=
  .lam 7 (.cond (.var 7) a (.app xs (.pred (.var 7))))

/-- Term for the positive branch `⟨1,u,x₁⟩` of Scott's bar operator. -/
def barPosTerm : Term :=
  seqConsTerm (.succ .zero)
    (seq2Term (.var 1) (.app (.var 2) (.succ .zero)))

/-- Closed terms for the two elementary semigroup generators. -/
def Rterm : Term := .lam 0 (seq2Term .zero (.var 0))

def Lterm : Term :=
  .lam 0
    (.app (.app (.var 0) (.succ .zero))
      (.app (.var 0) (.succ (.succ .zero))))

/-- **Scott 1976, (3.15).** Step of `ū = λx. x₀ ⊃ ⟨1, u, x₁⟩, overline{u(x₁)(x₂)}`. -/
def barStepBody (B u x : Pomega) : Pomega :=
  condSet (funOf x (ofNat 0)) (barPos u x)
    (funOf (funOf B (funOf u (funOf x (ofNat 1)))) (funOf x (ofNat 2)))

def barStep (B : Pomega) : Pomega :=
  graph (fun u => graph (fun x => barStepBody B u x))

/-- Closed term for the functional whose least fixed point is `barComb`. -/
def barStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.app (.var 2) .zero) barPosTerm
      (.app
        (.app (.var 0)
          (.app (.var 1) (.app (.var 2) (.succ .zero))))
        (.app (.var 2) (.succ (.succ .zero)))))))

/-- **Scott 1976, (3.15).** The bar combinator as a least fixed point. -/
def barComb : Pomega := fix barStep

/-- Composition in the semigroup `FUN`. -/
def enumComp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

/-- Scott's `Ḡ`. -/
def Gbar : Pomega := funOf barComb Gcomb

/-- The subsemigroup generated by `R`, `L`, and `Ḡ`. -/
inductive GeneratedSemigroup : Pomega → Prop
  | R : GeneratedSemigroup Rcomb
  | L : GeneratedSemigroup Lcomb
  | Gbar : GeneratedSemigroup Gbar
  | comp {u v} : GeneratedSemigroup u → GeneratedSemigroup v →
      GeneratedSemigroup (enumComp u v)

/-- Closed term for Scott's function-space retract `λu λx. u(x)`. -/
def funRetractTerm : Term :=
  .lam 0 (.lam 1 (.app (.var 0) (.var 1)))

/-- The least combinatory subalgebra containing every member of `xs`. -/
def GeneratedSubalgebra (xs : List Pomega) : Set Pomega :=
  {u | ∀ A : Set Pomega, IsSubalgebra A →
    (∀ x, x ∈ xs → x ∈ A) → u ∈ A}

/-- **Scott 1976, (4.46).** `vaal` on trees, companion of `val`. -/
def vaalF (v : Pomega) : Pomega :=
  graph (fun x =>
    condSet (funOf x (ofNat 0)) Gcomb
      (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
        (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1)))))

def vaalC : Pomega := fix vaalF

/-- Closed terms for the five packed combinators of `G`. Binders avoid
slot 8 so they can be placed inside `seq2Term`. -/
def sucClosed : Term := .lam 4 (.succ (.var 4))
def predClosed : Term := .lam 4 (.pred (.var 4))
def condClosed : Term :=
  .lam 4 (.lam 5 (.lam 6 (.cond (.var 6) (.var 4) (.var 5))))
def kClosed : Term := .lam 4 (.lam 5 (.var 4))
def sClosed : Term :=
  .lam 4 (.lam 5 (.lam 6
    (.app (.app (.var 4) (.var 6)) (.app (.var 5) (.var 6)))))

def gpackClosed : Term :=
  seq2Term sucClosed
    (seq2Term predClosed
      (seq2Term condClosed (seq2Term kClosed sClosed)))

def gClosed : Term := .lam 3 (.cond (.var 3) gpackClosed .zero)

/-- Closed term for the functional whose least fixed point is `vaal`. -/
def vaalStepTerm : Term :=
  .lam 0 (.lam 1
    (.cond (.app (.var 1) .zero) gClosed
      (.app
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))))

/-- **Scott 1976, (4.46).** `vaal : tree → id` as a typed map. -/
def vaalTyped : Pomega := funOf (arrowR treeR Icomb) vaalC

/-- **Scott 1976, TOT.** Graphs of total number-theoretic functions:
`$`-invariant and integer-valued on integers. -/
def TOT : Set Pomega :=
  {u | u = funOf dollarC u ∧ ∀ n, ∃ k, funOf u (ofNat n) = ofNat k}
end DomainTheory.DataTypesAsLattices
