/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Sum
import Mathlib.Data.Finset.Card

/-!
# Factoid 8.2 — λ-calculus model `D ≅ A + (D → D)`

**Scott 1982, §8.** `D` and `Con_D` are mutually recursive. Lean rejects putting the
FunCon-style clause (7) inside an inductive (negative occurrence), so the primary
path uses well-founded **`LamConDepth`** (`termination_by finsetMaxDepth`) and
inductive **`LamEntDepth`** (Scott (8)–(11)). Staged `LamConN` / early `LamToken`
remain scaffolding only.

**Status:** Def 2.1 packaged as `lambdaSystem` on `LamDToken` (depth WF); domain
equation via `lamUnfold` / `lamRhs` into `sumSystem A (functionSystem D D)`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

/-! ## Raw tokens + decidable equality -/

inductive RawLamToken (α : Type*) where
  | bot : RawLamToken α
  | atom : α → RawLamToken α
  | funTok : List (RawLamToken α) → List (RawLamToken α) → RawLamToken α

def listToFinset {β : Type*} [DecidableEq β] : List β → Finset β
  | [] => ∅
  | x :: xs => insert x (listToFinset xs)

theorem mem_listToFinset {β : Type*} [DecidableEq β] {x : β} {xs : List β} :
    x ∈ listToFinset xs ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact False.elim (Finset.notMem_empty x h)
    · intro h; cases h
  | cons a as ih =>
    simp only [listToFinset, Finset.mem_insert, List.mem_cons, ih]

mutual
  def rawLamBEq : RawLamToken α → RawLamToken α → Bool
    | .bot, .bot => true
    | .atom x, .atom y => decide (x = y)
    | .funTok u v, .funTok u' v' => rawLamListBEq u u' && rawLamListBEq v v'
    | _, _ => false
  def rawLamListBEq : List (RawLamToken α) → List (RawLamToken α) → Bool
    | [], [] => true
    | x :: xs, y :: ys => rawLamBEq x y && rawLamListBEq xs ys
    | _, _ => false
end

mutual
  theorem rawLamBEq_eq : ∀ a b : RawLamToken α, rawLamBEq a b = true ↔ a = b
  | .bot, .bot => by simp [rawLamBEq]
  | .atom x, .atom y => by
      simp only [rawLamBEq, decide_eq_true_eq]
      exact ⟨congrArg RawLamToken.atom, RawLamToken.atom.inj⟩
  | .funTok u v, .funTok u' v' => by
      simp only [rawLamBEq, Bool.and_eq_true]
      constructor
      · intro ⟨hu, hv⟩
        rw [(rawLamListBEq_eq u u').1 hu, (rawLamListBEq_eq v v').1 hv]
      · intro h
        injection h with hu hv
        subst hu; subst hv
        exact ⟨(rawLamListBEq_eq u u).2 rfl, (rawLamListBEq_eq v v).2 rfl⟩
  | .bot, .atom _ | .bot, .funTok _ _ | .atom _, .bot | .atom _, .funTok _ _
  | .funTok _ _, .bot | .funTok _ _, .atom _ => by
      constructor
      · intro h; simp [rawLamBEq] at h
      · intro h; cases h
  theorem rawLamListBEq_eq : ∀ u v : List (RawLamToken α), rawLamListBEq u v = true ↔ u = v
  | [], [] => by simp [rawLamListBEq]
  | x :: xs, y :: ys => by
      simp only [rawLamListBEq, Bool.and_eq_true]
      constructor
      · intro ⟨hx, hxs⟩
        rw [(rawLamBEq_eq x y).1 hx, (rawLamListBEq_eq xs ys).1 hxs]
      · intro h
        injection h with hx hxs
        subst hx; subst hxs
        exact ⟨(rawLamBEq_eq x x).2 rfl, (rawLamListBEq_eq xs xs).2 rfl⟩
  | [], _ :: _ | _ :: _, [] => by
      constructor
      · intro h; simp [rawLamListBEq] at h
      · intro h; cases h
end

instance : DecidableEq (RawLamToken α) := fun a b =>
  if h : rawLamBEq a b = true then isTrue ((rawLamBEq_eq a b).1 h)
  else isFalse fun hab => h ((rawLamBEq_eq a b).2 hab)

/-! ## Projections -/

private def lamAtomInsert : RawLamToken α → Finset α → Finset α
  | .atom x => insert x
  | .bot | .funTok _ _ => id

private def lamFunInsert :
    RawLamToken α → Finset (List (RawLamToken α) × List (RawLamToken α)) →
      Finset (List (RawLamToken α) × List (RawLamToken α))
  | .funTok u v => insert (u, v)
  | .bot | .atom _ => id

private instance : LeftCommutative (lamAtomInsert : RawLamToken α → Finset α → Finset α) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance : LeftCommutative
    (lamFunInsert : RawLamToken α →
      Finset (List (RawLamToken α) × List (RawLamToken α)) →
        Finset (List (RawLamToken α) × List (RawLamToken α))) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def lamAtomFinset (u : Finset (RawLamToken α)) : Finset α :=
  Multiset.foldr lamAtomInsert ∅ u.1

def lamFunFinset (u : Finset (RawLamToken α)) :
    Finset (List (RawLamToken α) × List (RawLamToken α)) :=
  Multiset.foldr lamFunInsert ∅ u.1

theorem mem_lamAtomFinset {u : Finset (RawLamToken α)} {x : α} :
    x ∈ lamAtomFinset u ↔ .atom x ∈ u := by
  have aux (s : Multiset (RawLamToken α)) :
      x ∈ Multiset.foldr lamAtomInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .atom x := by
    refine Multiset.induction_on s ?_ ?_
    · constructor
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p t ih
      cases p with
      | atom a =>
        simp only [Multiset.foldr_cons, lamAtomInsert, Finset.mem_insert, ih, Multiset.mem_cons]
        constructor
        · rintro (hx | ⟨q, hq, hq'⟩)
          · exact ⟨.atom a, Or.inl rfl, congrArg RawLamToken.atom hx.symm⟩
          · exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · injection hq' with hx; exact Or.inl hx.symm
          · exact Or.inr ⟨q, hq, hq'⟩
      | bot | funTok _ _ =>
        simp only [Multiset.foldr_cons, lamAtomInsert, id_eq, ih, Multiset.mem_cons]
        constructor
        · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · exact False.elim (nomatch hq')
          · exact ⟨q, hq, hq'⟩
  constructor
  · intro hx
    rcases (aux u.1).1 hx with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro hx
    exact (aux u.1).2 ⟨.atom x, Finset.mem_def.1 hx, rfl⟩

theorem mem_lamFunFinset {u : Finset (RawLamToken α)}
    {p : List (RawLamToken α) × List (RawLamToken α)} :
    p ∈ lamFunFinset u ↔ .funTok p.1 p.2 ∈ u := by
  have aux (s : Multiset (RawLamToken α)) :
      p ∈ Multiset.foldr lamFunInsert ∅ s ↔ ∃ t ∈ s, t = .funTok p.1 p.2 := by
    refine Multiset.induction_on s ?_ ?_
    · constructor
      · intro hp; exact False.elim (Finset.notMem_empty p hp)
      · rintro ⟨_, ht, _⟩; exact False.elim (by cases ht)
    · intro t rest ih
      cases t with
      | funTok u v =>
        simp only [Multiset.foldr_cons, lamFunInsert, Finset.mem_insert, ih, Multiset.mem_cons]
        constructor
        · rintro (hp | ⟨q, hq, hq'⟩)
          · exact ⟨.funTok u v, Or.inl rfl, by cases hp; rfl⟩
          · exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · injection hq' with hu hv
            exact Or.inl (Prod.ext hu.symm hv.symm)
          · exact Or.inr ⟨q, hq, hq'⟩
      | bot | atom _ =>
        simp only [Multiset.foldr_cons, lamFunInsert, id_eq, ih, Multiset.mem_cons]
        constructor
        · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · exact False.elim (nomatch hq')
          · exact ⟨q, hq, hq'⟩
  constructor
  · intro hp
    rcases (aux u.1).1 hp with ⟨t, ht, ht'⟩
    subst ht'; exact Finset.mem_def.2 ht
  · intro hp
    exact (aux u.1).2 ⟨.funTok p.1 p.2, Finset.mem_def.1 hp, rfl⟩

theorem lamAtomFinset_empty : lamAtomFinset (∅ : Finset (RawLamToken α)) = ∅ := rfl
theorem lamFunFinset_empty : lamFunFinset (∅ : Finset (RawLamToken α)) = ∅ := rfl

theorem lamAtomFinset_mono {u v : Finset (RawLamToken α)} (h : v ⊆ u) :
    lamAtomFinset v ⊆ lamAtomFinset u :=
  fun _ hx => mem_lamAtomFinset.2 (h (mem_lamAtomFinset.1 hx))

theorem lamFunFinset_mono {u v : Finset (RawLamToken α)} (h : v ⊆ u) :
    lamFunFinset v ⊆ lamFunFinset u :=
  fun _ hp => mem_lamFunFinset.2 (h (mem_lamFunFinset.1 hp))

theorem lamAtomFinset_insert_bot (u : Finset (RawLamToken α)) :
    lamAtomFinset (insert (.bot : RawLamToken α) u) = lamAtomFinset u := by
  ext x; simp only [mem_lamAtomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamAtomFinset_insert_atom (u : Finset (RawLamToken α)) (x : α) :
    lamAtomFinset (insert (.atom x) u) = insert x (lamAtomFinset u) := by
  ext y; simp only [Finset.mem_insert, mem_lamAtomFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (RawLamToken.atom.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem lamAtomFinset_insert_funTok (u : Finset (RawLamToken α))
    (xs ys : List (RawLamToken α)) :
    lamAtomFinset (insert (.funTok xs ys) u) = lamAtomFinset u := by
  ext x; simp only [mem_lamAtomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamFunFinset_insert_bot (u : Finset (RawLamToken α)) :
    lamFunFinset (insert (.bot : RawLamToken α) u) = lamFunFinset u := by
  ext p; simp only [mem_lamFunFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamFunFinset_insert_atom (u : Finset (RawLamToken α)) (x : α) :
    lamFunFinset (insert (.atom x) u) = lamFunFinset u := by
  ext p; simp only [mem_lamFunFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamFunFinset_insert_funTok (u : Finset (RawLamToken α))
    (xs ys : List (RawLamToken α)) :
    lamFunFinset (insert (.funTok xs ys) u) = insert (xs, ys) (lamFunFinset u) := by
  ext p; simp only [Finset.mem_insert, mem_lamFunFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (Prod.ext (RawLamToken.funTok.inj h).1 (RawLamToken.funTok.inj h).2)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

private def lamInUnionInsert [DecidableEq (RawLamToken α)] :
    List (RawLamToken α) × List (RawLamToken α) → Finset (RawLamToken α) →
      Finset (RawLamToken α)
  | p, acc => listToFinset p.1 ∪' acc

private def lamOutUnionInsert [DecidableEq (RawLamToken α)] :
    List (RawLamToken α) × List (RawLamToken α) → Finset (RawLamToken α) →
      Finset (RawLamToken α)
  | p, acc => listToFinset p.2 ∪' acc

private instance [DecidableEq (RawLamToken α)] :
    LeftCommutative (lamInUnionInsert (α := α)) :=
  ⟨fun p q s => by
    simp only [lamInUnionInsert]
    ext x; simp only [mem_funion]
    constructor <;> · rintro (h | h | h); exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]⟩

private instance [DecidableEq (RawLamToken α)] :
    LeftCommutative (lamOutUnionInsert (α := α)) :=
  ⟨fun p q s => by
    simp only [lamOutUnionInsert]
    ext x; simp only [mem_funion]
    constructor <;> · rintro (h | h | h); exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]⟩

def lamInputUnion (s : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    Finset (RawLamToken α) :=
  Multiset.foldr (lamInUnionInsert (α := α)) ∅ s.1

def lamOutputUnion (s : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    Finset (RawLamToken α) :=
  Multiset.foldr (lamOutUnionInsert (α := α)) ∅ s.1

theorem lamInputUnion_empty :
    lamInputUnion (∅ : Finset (List (RawLamToken α) × List (RawLamToken α))) = ∅ := by
  rfl

theorem lamOutputUnion_empty :
    lamOutputUnion (∅ : Finset (List (RawLamToken α) × List (RawLamToken α))) = ∅ := by
  rfl

theorem mem_lamInputUnion {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    {t : RawLamToken α} :
    t ∈ lamInputUnion s ↔ ∃ p ∈ s, t ∈ listToFinset p.1 := by
  have aux (m : Multiset (List (RawLamToken α) × List (RawLamToken α))) :
      t ∈ Multiset.foldr (lamInUnionInsert (α := α)) ∅ m ↔
        ∃ p ∈ m, t ∈ listToFinset p.1 := by
    refine Multiset.induction_on m ?_ ?_
    · constructor
      · intro ht; exact False.elim (Finset.notMem_empty t ht)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p rest ih
      simp only [Multiset.foldr_cons, lamInUnionInsert, mem_funion, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, Or.inl rfl, ht⟩
        · exact ⟨q, Or.inr hq, ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩
  simpa [lamInputUnion] using aux s.1

theorem mem_lamOutputUnion {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    {t : RawLamToken α} :
    t ∈ lamOutputUnion s ↔ ∃ p ∈ s, t ∈ listToFinset p.2 := by
  have aux (m : Multiset (List (RawLamToken α) × List (RawLamToken α))) :
      t ∈ Multiset.foldr (lamOutUnionInsert (α := α)) ∅ m ↔
        ∃ p ∈ m, t ∈ listToFinset p.2 := by
    refine Multiset.induction_on m ?_ ?_
    · constructor
      · intro ht; exact False.elim (Finset.notMem_empty t ht)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p rest ih
      simp only [Multiset.foldr_cons, lamOutUnionInsert, mem_funion, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, Or.inl rfl, ht⟩
        · exact ⟨q, Or.inr hq, ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩
  simpa [lamOutputUnion] using aux s.1

/-! ## Staged consistency -/

variable (A : InfoSys α)

/-- Stage-`n` consistency (Scott (4)–(7), stratified). -/
def LamConN : ℕ → Finset (RawLamToken α) → Prop
  | 0, u => lamAtomFinset u ∈ A.Con ∧ lamFunFinset u = ∅
  | n + 1, u =>
      LamConN n u ∨
        (lamAtomFinset u = ∅ ∧
          (∀ p ∈ lamFunFinset u,
            LamConN n (listToFinset p.1) ∧ LamConN n (listToFinset p.2)) ∧
            ∀ s ⊆ lamFunFinset u,
              LamConN n (lamInputUnion s) → LamConN n (lamOutputUnion s))

def LamCon (u : Finset (RawLamToken α)) : Prop :=
  ∃ n, LamConN A n u

/-- Well-formed tokens (Scott (1)–(3)). -/
def IsLamToken : RawLamToken α → Prop
  | .bot | .atom _ => True
  | .funTok u v => LamCon A (listToFinset u) ∧ LamCon A (listToFinset v)

def LamToken : Type _ := { t : RawLamToken α // IsLamToken A t }

instance : DecidableEq (LamToken A) := Subtype.instDecidableEq

def lamBot : LamToken A := ⟨.bot, trivial⟩

def lamForget (t : LamToken A) : RawLamToken α := t.val

private def lamForgetInsert :
    LamToken A → Finset (RawLamToken α) → Finset (RawLamToken α) :=
  fun t => insert (lamForget A t)

private instance : LeftCommutative (lamForgetInsert (A := A)) :=
  ⟨fun p q s => insert_comm' (lamForget A p) (lamForget A q) s⟩

def lamForgetFinset (u : Finset (LamToken A)) : Finset (RawLamToken α) :=
  Multiset.foldr (lamForgetInsert (A := A)) ∅ u.1

theorem mem_foldr_lamForget (s : Multiset (LamToken A)) (t : RawLamToken α) :
    t ∈ Multiset.foldr (lamForgetInsert (A := A)) ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, lamForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem lamAtomFinset_singleton_funTok (u v : List (RawLamToken α)) :
    lamAtomFinset ({.funTok u v} : Finset (RawLamToken α)) = ∅ := by
  ext x
  constructor
  · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
  · intro hx; exact False.elim (Finset.notMem_empty x hx)

theorem lamFunFinset_singleton_funTok (u v : List (RawLamToken α)) :
    lamFunFinset ({.funTok u v} : Finset (RawLamToken α)) = {(u, v)} := by
  ext p
  simp only [mem_lamFunFinset, Finset.mem_singleton]
  constructor
  · intro h
    exact Prod.ext (RawLamToken.funTok.inj h).1 (RawLamToken.funTok.inj h).2
  · intro h
    cases h
    rfl

theorem lamInputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamInputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.1 := by
  ext t
  change t ∈ listToFinset p.1 ∪' ∅ ↔ t ∈ listToFinset p.1
  simp only [mem_funion, Finset.notMem_empty, or_false]

theorem lamOutputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.2 := by
  ext t
  change t ∈ listToFinset p.2 ∪' ∅ ↔ t ∈ listToFinset p.2
  simp only [mem_funion, Finset.notMem_empty, or_false]

/-- Bundled consistency on `LamToken` finsets. -/
def LamTokenCon (u : Finset (LamToken A)) : Prop :=
  LamCon A (lamForgetFinset A u)

/-! ## Staged entailment (Scott (8)–(11)) — definitions only

Full `ent_refl` / `ent_con` / `ent_trans` for the `InfoSys` instance remain; the
definitions below package Scott’s clauses (8)–(11) at stages matching `LamConN`.
-/

/-- Stage-`n` entailment on raw tokens (Scott (8)–(11), stratified). -/
def LamEntN : ℕ → Finset (RawLamToken α) → RawLamToken α → Prop
  | 0, u, .bot => LamConN A 0 u
  | 0, u, .atom x =>
      LamConN A 0 u ∧ lamAtomFinset u ≠ ∅ ∧ A.Ent (lamAtomFinset u) x
  | 0, _, .funTok _ _ => False
  | n + 1, u, t =>
      LamEntN n u t ∨
        match t with
        | .bot => LamConN A (n + 1) u
        | .atom x =>
            LamConN A (n + 1) u ∧ lamFunFinset u = ∅ ∧
              lamAtomFinset u ≠ ∅ ∧ A.Ent (lamAtomFinset u) x
        | .funTok u' v' =>
            LamConN A (n + 1) u ∧ lamAtomFinset u = ∅ ∧
              LamConN A n (listToFinset u') ∧ LamConN A n (listToFinset v') ∧
              ∃ s ⊆ lamFunFinset u,
                (∀ p ∈ s, ∀ t ∈ listToFinset p.1, LamEntN n (listToFinset u') t) ∧
                  (∀ t ∈ listToFinset v', LamEntN n (lamOutputUnion s) t)

/-- Unstaged raw entailment. -/
def LamEnt (u : Finset (RawLamToken α)) (t : RawLamToken α) : Prop :=
  ∃ n, LamEntN A n u t

/-! ## Inversion lemmas for staged Con -/

/-- Bundled entailment on `LamToken`. -/
def LamTokenEnt (u : Finset (LamToken A)) (p : LamToken A) : Prop :=
  LamEnt A (lamForgetFinset A u) p.val

/-! ## ent_con: inserting an entailed token preserves consistency -/

theorem lamInputUnion_insert
    (s : Finset (List (RawLamToken α) × List (RawLamToken α)))
    (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamInputUnion (insert p s) = listToFinset p.1 ∪' lamInputUnion s := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamInputUnion).1 ht with ⟨q, hq, ht'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_funion.2 (Or.inl ht')
    · exact mem_funion.2 (Or.inr ((mem_lamInputUnion).2 ⟨q, hq, ht'⟩))
  · intro ht
    rcases mem_funion.1 ht with ht | ht
    · exact (mem_lamInputUnion).2 ⟨p, Finset.mem_insert_self p s, ht⟩
    · rcases (mem_lamInputUnion).1 ht with ⟨q, hq, ht'⟩
      exact (mem_lamInputUnion).2 ⟨q, Finset.mem_insert_of_mem hq, ht'⟩

theorem lamOutputUnion_insert
    (s : Finset (List (RawLamToken α) × List (RawLamToken α)))
    (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion (insert p s) = listToFinset p.2 ∪' lamOutputUnion s := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamOutputUnion).1 ht with ⟨q, hq, ht'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_funion.2 (Or.inl ht')
    · exact mem_funion.2 (Or.inr ((mem_lamOutputUnion).2 ⟨q, hq, ht'⟩))
  · intro ht
    rcases mem_funion.1 ht with ht | ht
    · exact (mem_lamOutputUnion).2 ⟨p, Finset.mem_insert_self p s, ht⟩
    · rcases (mem_lamOutputUnion).1 ht with ⟨q, hq, ht'⟩
      exact (mem_lamOutputUnion).2 ⟨q, Finset.mem_insert_of_mem hq, ht'⟩

theorem lamInputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamInputUnion (s ∪' t) = lamInputUnion s ∪' lamInputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.1 hp with hp | hp
    · exact mem_funion.2 (Or.inl ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.2 (Or.inr ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.1 hx with hx | hx
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, mem_funion.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, mem_funion.2 (Or.inr hp), hx'⟩

theorem lamOutputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamOutputUnion (s ∪' t) = lamOutputUnion s ∪' lamOutputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.1 hp with hp | hp
    · exact mem_funion.2 (Or.inl ((mem_lamOutputUnion).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.2 (Or.inr ((mem_lamOutputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.1 hx with hx | hx
    · rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamOutputUnion).2 ⟨p, mem_funion.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamOutputUnion).2 ⟨p, mem_funion.2 (Or.inr hp), hx'⟩

/-! ## Depth measure (for well-founded Con) -/

private theorem max_le_max_nat {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d :=
  max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))


def rawDepth : RawLamToken α → ℕ
  | .bot | .atom _ => 0
  | .funTok u v =>
      1 + Nat.max
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v)

theorem foldl_max_mono_init {u : List (RawLamToken α)} {i j : ℕ} (hij : i ≤ j) :
    List.foldl (fun d t => Nat.max d (rawDepth t)) i u ≤
      List.foldl (fun d t => Nat.max d (rawDepth t)) j u := by
  induction u generalizing i j with
  | nil => exact hij
  | cons a as ih => exact ih (max_le_max_nat hij le_rfl)

theorem foldl_max_ge_init (u : List (RawLamToken α)) (init : ℕ) :
    init ≤ List.foldl (fun d t => Nat.max d (rawDepth t)) init u := by
  induction u generalizing init with
  | nil => exact le_rfl
  | cons a as ih =>
    exact Nat.le_trans (Nat.le_max_left init (rawDepth a)) (ih _)

theorem foldl_list_le_of_mem {t : RawLamToken α} {u : List (RawLamToken α)}
    (ht : t ∈ u) :
    rawDepth t ≤ List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u := by
  induction u with
  | nil => cases ht
  | cons a as ih =>
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right 0 (rawDepth t))
        (foldl_max_ge_init as (Nat.max 0 (rawDepth t)))
    · exact Nat.le_trans (ih ht) (foldl_max_mono_init (Nat.zero_le _))

theorem rawDepth_funTok_gt_left {u v : List (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ u) : rawDepth t < rawDepth (.funTok u v) := by
  have h : rawDepth t ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_trans (foldl_list_le_of_mem ht) (Nat.le_max_left _ _)
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt h (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

theorem rawDepth_funTok_gt_right {u v : List (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ v) : rawDepth t < rawDepth (.funTok u v) := by
  have h : rawDepth t ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_trans (foldl_list_le_of_mem ht) (Nat.le_max_right _ _)
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt h (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

private def maxDepthInsert : RawLamToken α → ℕ → ℕ :=
  fun t d => Nat.max (rawDepth t) d

private instance : LeftCommutative (maxDepthInsert (α := α)) :=
  ⟨fun a b d => by simp only [maxDepthInsert]; exact Nat.max_left_comm _ _ _⟩

def finsetMaxDepth (u : Finset (RawLamToken α)) : ℕ :=
  Multiset.foldr (maxDepthInsert (α := α)) 0 u.1

theorem le_finsetMaxDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ u) : rawDepth t ≤ finsetMaxDepth u := by
  simp only [finsetMaxDepth]
  have ht' : t ∈ u.1 := Finset.mem_def.1 ht
  revert ht'
  refine Multiset.induction_on u.1 ?_ ?_
  · intro ht'; cases ht'
  · intro a s ih ht'
    simp only [Multiset.mem_cons] at ht'
    simp only [Multiset.foldr_cons, maxDepthInsert]
    rcases ht' with rfl | ht'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht') (Nat.le_max_right _ _)

theorem foldr_max_le_of_forall {s : Multiset (RawLamToken α)} {b : ℕ}
    (h : ∀ t ∈ s, rawDepth t ≤ b) :
    Multiset.foldr (maxDepthInsert (α := α)) 0 s ≤ b := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro; exact Nat.zero_le _
  · intro a s ih h
    simp only [Multiset.foldr_cons, maxDepthInsert]
    exact Nat.max_le.2 ⟨h a (Multiset.mem_cons_self _ _),
      ih fun t ht => h t (Multiset.mem_cons_of_mem ht)⟩

theorem foldr_max_lt_of_forall {s : Multiset (RawLamToken α)} {b : ℕ}
    (hb : 0 < b) (h : ∀ t ∈ s, rawDepth t < b) :
    Multiset.foldr (maxDepthInsert (α := α)) 0 s < b := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro; exact hb
  · intro a s ih h
    simp only [Multiset.foldr_cons, maxDepthInsert]
    exact Nat.max_lt.2 ⟨h a (Multiset.mem_cons_self _ _),
      ih fun t ht => h t (Multiset.mem_cons_of_mem ht)⟩

theorem finsetMaxDepth_listToFinset_le (u : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) ≤
      List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u := by
  simp only [finsetMaxDepth]
  exact foldr_max_le_of_forall fun t ht =>
    foldl_list_le_of_mem ((mem_listToFinset).1 (Finset.mem_def.2 ht))

theorem finsetMaxDepth_list_lt_funTok (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth_listToFinset_le u
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_left _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

theorem finsetMaxDepth_list_lt_funTok_out (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset v) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth_listToFinset_le v
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_right _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))


theorem finsetMaxDepth_of_mem_funTok {u : Finset (RawLamToken α)}
    {xs ys : List (RawLamToken α)} (h : .funTok xs ys ∈ u) :
    finsetMaxDepth (listToFinset xs) < finsetMaxDepth u ∧
      finsetMaxDepth (listToFinset ys) < finsetMaxDepth u :=
  ⟨Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok xs ys) (le_finsetMaxDepth_of_mem h),
    Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok_out xs ys) (le_finsetMaxDepth_of_mem h)⟩

theorem finsetMaxDepth_inputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamInputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamInputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamInputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamInputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_left ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

theorem finsetMaxDepth_outputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamOutputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamOutputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamOutputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamOutputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_right ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

/-- Depth-based consistency: FunCon in the recursive clause (Scott (7)).
Uses `decidableEq_finset` so the empty-fun branch does not pull `Classical.choice`. -/
def LamConDepth (u : Finset (RawLamToken α)) : Prop :=
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  if _hF : lamFunFinset u = ∅ then
    lamAtomFinset u ∈ A.Con
  else
    lamAtomFinset u = ∅ ∧
      (∀ p ∈ lamFunFinset u,
        LamConDepth (listToFinset p.1) ∧ LamConDepth (listToFinset p.2)) ∧
      (∀ s ⊆ lamFunFinset u,
        LamConDepth (lamInputUnion s) → LamConDepth (lamOutputUnion s))
termination_by finsetMaxDepth u
decreasing_by
  · exact (finsetMaxDepth_of_mem_funTok (mem_lamFunFinset.1 ‹_›)).1
  · exact (finsetMaxDepth_of_mem_funTok (mem_lamFunFinset.1 ‹_›)).2
  · exact finsetMaxDepth_inputUnion_lt ‹_› ‹_›
  · exact finsetMaxDepth_outputUnion_lt ‹_› ‹_›

theorem LamConDepth_empty : LamConDepth A (∅ : Finset (RawLamToken α)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dite_eq_left lamFunFinset_empty, lamAtomFinset_empty]
  exact A.con_empty

theorem LamConDepth_of_fun_empty {u : Finset (RawLamToken α)}
    (hF : lamFunFinset u = ∅) :
    LamConDepth A u ↔ lamAtomFinset u ∈ A.Con := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dite_eq_left hF]

theorem LamConDepth_of_fun_nonempty {u : Finset (RawLamToken α)}
    (hF : lamFunFinset u ≠ ∅) :
    LamConDepth A u ↔
      lamAtomFinset u = ∅ ∧
        (∀ p ∈ lamFunFinset u,
          LamConDepth A (listToFinset p.1) ∧ LamConDepth A (listToFinset p.2)) ∧
        (∀ s ⊆ lamFunFinset u,
          LamConDepth A (lamInputUnion s) → LamConDepth A (lamOutputUnion s)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dite_eq_right hF]

theorem LamConDepth_mono {u v : Finset (RawLamToken α)}
    (huv : u ⊆ v) (hv : LamConDepth A v) : LamConDepth A u := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hFunMono := lamFunFinset_mono huv
  have hAtomMono := lamAtomFinset_mono huv
  by_cases hFv : lamFunFinset v = ∅
  · have hFu : lamFunFinset u = ∅ :=
      Finset.Subset.antisymm
        (fun p hp => by
          have := hFunMono hp
          rw [hFv] at this; exact False.elim (Finset.notMem_empty p this))
        (Finset.empty_subset _)
    exact (LamConDepth_of_fun_empty A hFu).2
      (A.con_subset ((LamConDepth_of_fun_empty A hFv).1 hv) hAtomMono)
  · have hv' := (LamConDepth_of_fun_nonempty A hFv).1 hv
    rcases hv' with ⟨hAv, hWF, hFun⟩
    by_cases hFu : lamFunFinset u = ∅
    · have hAu : lamAtomFinset u = ∅ :=
        Finset.Subset.antisymm
          (fun x hx => by
            have := hAtomMono hx
            rw [hAv] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      exact (LamConDepth_of_fun_empty A hFu).2 (by rw [hAu]; exact A.con_empty)
    · refine (LamConDepth_of_fun_nonempty A hFu).2 ⟨?_, ?_, ?_⟩
      · exact Finset.Subset.antisymm
          (fun x hx => by
            have := hAtomMono hx
            rw [hAv] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      · intro p hp; exact hWF p (hFunMono hp)
      · intro s hs hIn
        exact hFun s (fun p hp => hFunMono (hs hp)) hIn

theorem LamConDepth_singleton_bot :
    LamConDepth A ({.bot} : Finset (RawLamToken α)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
    ext p; constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)
  exact (LamConDepth_of_fun_empty A hF).2 (by
    have h : lamAtomFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    rw [h]; exact A.con_empty)

theorem LamConDepth_singleton_atom (x : α) :
    LamConDepth A ({.atom x} : Finset (RawLamToken α)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.atom x} : Finset (RawLamToken α)) = ∅ := by
    ext p; constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)
  exact (LamConDepth_of_fun_empty A hF).2 (by
    have h : lamAtomFinset ({.atom x} : Finset (RawLamToken α)) = {x} := by
      ext y; simp only [mem_lamAtomFinset, Finset.mem_singleton]
      exact ⟨RawLamToken.atom.inj, congrArg RawLamToken.atom⟩
    rw [h]; exact A.con_sing x)

/-! ## Depth-based entailment (Scott (8)–(11), inductive FunEnt-style) -/

/-- Depth-based entailment as an inductive Prop (Scott (8)–(11)).
Premises are positive, so FunEnt-style recursion is allowed — unlike FunCon
inside an inductive `LamCon`. -/
inductive LamEntDepth : Finset (RawLamToken α) → RawLamToken α → Prop where
  | bot {u : Finset (RawLamToken α)}
      (hu : LamConDepth A u) : LamEntDepth u .bot
  | atom {u : Finset (RawLamToken α)} {x : α}
      (hu : LamConDepth A u)
      (hF : lamFunFinset u = ∅)
      (hne : lamAtomFinset u ≠ ∅)
      (hEnt : A.Ent (lamAtomFinset u) x) : LamEntDepth u (.atom x)
  | funTok {u : Finset (RawLamToken α)} {xs ys : List (RawLamToken α)}
      {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
      (hu : LamConDepth A u)
      (hA : lamAtomFinset u = ∅)
      (hConIn : LamConDepth A (listToFinset xs))
      (hConOut : LamConDepth A (listToFinset ys))
      (hs : s ⊆ lamFunFinset u)
      /- Function tokens are only entailed in the function world (cf. `SumEnt` right). -/
      (hWorld : lamFunFinset u ≠ ∅)
      /- Atom/bot inputs only when `xs` is atom-world — blocks mixed-world FunCon gaps. -/
      (hInCompat : lamFunFinset (listToFinset xs) = ∅ →
        lamFunFinset (lamInputUnion s) = ∅)
      (hEntIn : ∀ p ∈ s, ∀ z ∈ listToFinset p.1, LamEntDepth (listToFinset xs) z)
      (hEntOut : ∀ z ∈ listToFinset ys, LamEntDepth (lamOutputUnion s) z) :
      LamEntDepth u (.funTok xs ys)

theorem LamEntDepth_con {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEntDepth A u t) : LamConDepth A u := by
  cases ht with
  | bot hu => exact hu
  | atom hu _ _ _ => exact hu
  | funTok hu _ _ _ _ _ _ _ _ => exact hu

theorem LamEntDepth_bot {u : Finset (RawLamToken α)} (hu : LamConDepth A u) :
    LamEntDepth A u .bot :=
  LamEntDepth.bot hu

theorem LamEntDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamConDepth A u) (ht : t ∈ u) : LamEntDepth A u t := by
  suffices ∀ M u t, Nat.max (finsetMaxDepth u) (rawDepth t) = M →
      LamConDepth A u → t ∈ u → LamEntDepth A u t from
    this _ _ _ rfl hu ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u t hM hu ht
    match t with
    | .bot => exact LamEntDepth_bot A hu
    | .atom x =>
      cases decidableEq_finset (lamFunFinset u) ∅ with
      | isTrue hF =>
        have hx : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
        exact LamEntDepth.atom hu hF (Finset.ne_empty_of_mem hx)
          (A.ent_refl ((LamConDepth_of_fun_empty A hF).1 hu) hx)
      | isFalse hF =>
        have hA := ((LamConDepth_of_fun_nonempty A hF).1 hu).1
        have hx : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
        rw [hA] at hx; exact False.elim (Finset.notMem_empty x hx)
    | .funTok xs ys =>
      cases decidableEq_finset (lamFunFinset u) ∅ with
      | isTrue hF =>
        have : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        rw [hF] at this; exact False.elim (Finset.notMem_empty _ this)
      | isFalse hF =>
        have hu' := (LamConDepth_of_fun_nonempty A hF).1 hu
        rcases hu' with ⟨hA, hWF, _hFun⟩
        have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        have ⟨hConIn, hConOut⟩ := hWF (xs, ys) hmem
        refine LamEntDepth.funTok (s := {(xs, ys)}) hu hA hConIn hConOut
          (fun p hp => by
            have hp' : p = (xs, ys) := Finset.mem_singleton.mp hp
            exact hp' ▸ hmem) hF ?_ ?_ ?_
        · intro hxsF
          have hIn : lamInputUnion {(xs, ys)} = listToFinset xs := by
            rw [lamInputUnion_singleton]
          rw [hIn, hxsF]
        · intro p hp z hz
          have hp' : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst hp'
          refine ih (Nat.max (finsetMaxDepth (listToFinset xs)) (rawDepth z))
            ?_ (listToFinset xs) z rfl hConIn hz
          have htok : .funTok xs ys ∈ u := mem_lamFunFinset.1 hmem
          have ht_lt : rawDepth z < finsetMaxDepth u :=
            Nat.lt_of_lt_of_le (rawDepth_funTok_gt_left ((mem_listToFinset).1 hz))
              (le_finsetMaxDepth_of_mem htok)
          have hxs_lt : finsetMaxDepth (listToFinset xs) < rawDepth (.funTok xs ys) :=
            finsetMaxDepth_list_lt_funTok xs ys
          rw [← hM]
          refine Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le hxs_lt (Nat.le_max_right _ _),
            Nat.lt_of_lt_of_le ht_lt (Nat.le_max_left _ _)⟩
        · intro z hz
          rw [lamOutputUnion_singleton]
          refine ih (Nat.max (finsetMaxDepth (listToFinset ys)) (rawDepth z))
            ?_ (listToFinset ys) z rfl hConOut hz
          have ht_lt : rawDepth z < rawDepth (.funTok xs ys) :=
            rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)
          have hys_lt : finsetMaxDepth (listToFinset ys) < rawDepth (.funTok xs ys) :=
            finsetMaxDepth_list_lt_funTok_out xs ys
          rw [← hM]
          refine Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le hys_lt (Nat.le_max_right _ _),
            Nat.lt_of_lt_of_le ht_lt (Nat.le_max_right _ _)⟩

/-- Inserting bot preserves depth-Con. -/
theorem LamConDepth_insert_bot {u : Finset (RawLamToken α)}
    (hu : LamConDepth A u) :
    LamConDepth A (insert (.bot : RawLamToken α) u) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  by_cases hF : lamFunFinset u = ∅
  · have hF' : lamFunFinset (insert (.bot : RawLamToken α) u) = ∅ := by
      rw [lamFunFinset_insert_bot]; exact hF
    exact (LamConDepth_of_fun_empty A hF').2 (by
      rw [lamAtomFinset_insert_bot]
      exact (LamConDepth_of_fun_empty A hF).1 hu)
  · have hu' := (LamConDepth_of_fun_nonempty A hF).1 hu
    rcases hu' with ⟨hA, hWF, hFun⟩
    have hF' : lamFunFinset (insert (.bot : RawLamToken α) u) ≠ ∅ := by
      rw [lamFunFinset_insert_bot]; exact hF
    refine (LamConDepth_of_fun_nonempty A hF').2 ⟨?_, ?_, ?_⟩
    · rw [lamAtomFinset_insert_bot]; exact hA
    · intro p hp
      rw [lamFunFinset_insert_bot] at hp
      exact hWF p hp
    · intro s hs hIn
      refine hFun s (by rw [← lamFunFinset_insert_bot u]; exact hs) hIn

/-- Inserting an entailed atom preserves depth-Con. -/
theorem LamConDepth_insert_atom {u : Finset (RawLamToken α)} {x : α}
    (ht : LamEntDepth A u (.atom x)) :
    LamConDepth A (insert (.atom x) u) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  cases ht with
  | atom hu hF _hne hEnt =>
    have hF' : lamFunFinset (insert (.atom x) u) = ∅ := by
      rw [lamFunFinset_insert_atom]; exact hF
    exact (LamConDepth_of_fun_empty A hF').2 (by
      rw [lamAtomFinset_insert_atom]
      exact A.ent_con hEnt)

/-- Weaken entailment when the larger set stays in the function world (`atom = ∅`). -/
theorem LamEntDepth_weaken_fun {u v : Finset (RawLamToken α)} {t : RawLamToken α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hAv : lamAtomFinset v = ∅)
    (ht : LamEntDepth A u t) : LamEntDepth A v t := by
  cases ht with
  | bot _ => exact LamEntDepth.bot hv
  | atom _ _ hne _ =>
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
    exact False.elim (Finset.notMem_empty x (by
      have := lamAtomFinset_mono huv hx; rwa [hAv] at this))
  | funTok _ _ hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
    exact LamEntDepth.funTok hv hAv hConIn hConOut
      (fun p hp => lamFunFinset_mono huv (hs hp))
      (fun hFv => hWorld (Finset.Subset.antisymm
          (fun p hp => by
            have := lamFunFinset_mono huv hp
            rw [hFv] at this; exact False.elim (Finset.notMem_empty p this))
          (Finset.empty_subset _)))
      hInCompat hEntIn hEntOut

/-- Weaken atom-entailment when the larger set stays in the atom world (`fun = ∅`). -/
theorem LamEntDepth_weaken_atom {u v : Finset (RawLamToken α)} {x : α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hFv : lamFunFinset v = ∅)
    (ht : LamEntDepth A u (.atom x)) : LamEntDepth A v (.atom x) := by
  cases ht with
  | atom hu hF hne hEnt =>
    have hsubA := lamAtomFinset_mono huv
    have hne' : lamAtomFinset v ≠ ∅ := by
      intro hAv
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact Finset.notMem_empty y (by have := hsubA hy; rwa [hAv] at this)
    exact LamEntDepth.atom hv hFv hne'
      (A.ent_trans ((LamConDepth_of_fun_empty A hFv).1 hv)
        ((LamConDepth_of_fun_empty A hF).1 hu)
        (fun y hy => A.ent_refl ((LamConDepth_of_fun_empty A hFv).1 hv) (hsubA hy))
        hEnt)

/-! ### Funion / filter helpers + weaken_insert + funion_of_entSet + insert_of_ent -/

private theorem funion_empty_right_lam (u : Finset (RawLamToken α)) :
    u ∪' (∅ : Finset (RawLamToken α)) = u := by
  ext x; simp only [mem_funion, Finset.notMem_empty, or_false]

private theorem funion_insert_lam (u : Finset (RawLamToken α)) (a : RawLamToken α)
    (t : Finset (RawLamToken α)) : u ∪' insert a t = insert a (u ∪' t) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with hu | hins
    · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inl hu))
    · rcases Finset.mem_insert.mp hins with ha | ht
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inr ht))
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | h
    · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl ha)))
    · rcases mem_funion.mp h with hu | ht
      · exact mem_funion.mpr (Or.inl hu)
      · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ht)))

private theorem insert_filter_ne_lam
    {p : List (RawLamToken α) × List (RawLamToken α)}
    {t : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hp : p ∈ t) : insert p (t.filter (· ≠ p)) = t := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (Finset.mem_filter.mp hq).1
  · intro hq
    if h : q = p then
      exact Finset.mem_insert.mpr (Or.inl h)
    else
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hq, h⟩))

private theorem filter_ne_subset_of_subset_insert_lam
    {p : List (RawLamToken α) × List (RawLamToken α)}
    {t w : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (ht : t ⊆ insert p w) : t.filter (· ≠ p) ⊆ w := by
  intro q hq
  have ⟨hqt, hne⟩ := Finset.mem_filter.mp hq
  have : q ∈ insert p w := ht hqt
  rcases Finset.mem_insert.mp this with rfl | hqW
  · exact False.elim (hne rfl)
  · exact hqW

theorem lamFunFinset_funion (u v : Finset (RawLamToken α)) :
    lamFunFinset (u ∪' v) = lamFunFinset u ∪' lamFunFinset v := by
  ext p
  constructor
  · intro hp
    have : .funTok p.1 p.2 ∈ u ∪' v := mem_lamFunFinset.1 hp
    rcases mem_funion.1 this with hu | hv
    · exact mem_funion.2 (Or.inl (mem_lamFunFinset.2 hu))
    · exact mem_funion.2 (Or.inr (mem_lamFunFinset.2 hv))
  · intro hp
    rcases mem_funion.1 hp with hu | hv
    · exact mem_lamFunFinset.2 (mem_funion.2 (Or.inl (mem_lamFunFinset.1 hu)))
    · exact mem_lamFunFinset.2 (mem_funion.2 (Or.inr (mem_lamFunFinset.1 hv)))

/-- Weaken Ent across inserting another token entailed by the same set. -/
theorem LamEntDepth_weaken_insert {u : Finset (RawLamToken α)}
    {a x : RawLamToken α}
    (hu' : LamConDepth A (insert a u))
    (hx : LamEntDepth A u x) (ha : LamEntDepth A u a) :
    LamEntDepth A (insert a u) x := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have huv : u ⊆ insert a u := Finset.subset_insert a u
  match x with
  | .bot => exact LamEntDepth.bot hu'
  | .atom z =>
    cases decidableEq_finset (lamFunFinset (insert a u)) ∅ with
    | isTrue hF =>
      exact LamEntDepth_weaken_atom A huv hu' hF hx
    | isFalse hF =>
      have hAt := ((LamConDepth_of_fun_nonempty A hF).1 hu').1
      cases hx with
      | atom _ _ hne _ =>
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        exact False.elim (Finset.notMem_empty y (by
          have := lamAtomFinset_mono huv hy; rwa [hAt] at this))
  | .funTok xs ys =>
    cases decidableEq_finset (lamFunFinset (insert a u)) ∅ with
    | isFalse hF =>
      have hAv := ((LamConDepth_of_fun_nonempty A hF).1 hu').1
      exact LamEntDepth_weaken_fun A huv hu' hAv hx
    | isTrue hF =>
      cases ha with
      | bot _ =>
        cases hx with
        | funTok hu hA hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
          have hAv : lamAtomFinset (insert (.bot : RawLamToken α) u) = ∅ := by
            rw [lamAtomFinset_insert_bot]; exact hA
          exact LamEntDepth.funTok hu' hAv hConIn hConOut
            (by rw [lamFunFinset_insert_bot]; exact hs)
            (by rw [lamFunFinset_insert_bot]; exact hWorld)
            hInCompat hEntIn hEntOut
      | atom _ _ hne _ =>
        cases hx with
        | funTok _ hA _ _ _ _ _ _ _ =>
          obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
          exact False.elim (Finset.notMem_empty y (by rwa [hA] at hy))
      | funTok _ _ _ _ _ _ _ _ _ =>
        -- `a` refined to funTok, so fun (insert a u) ≠ ∅, contradicting hF
        simp only [lamFunFinset_insert_funTok] at hF
        exact False.elim (Finset.notMem_empty _ (hF ▸ Finset.mem_insert_self _ _))


private theorem finsetMaxDepth_insert_le (u : Finset (RawLamToken α)) (a : RawLamToken α) :
    finsetMaxDepth (insert a u) ≤ Nat.max (rawDepth a) (finsetMaxDepth u) := by
  refine foldr_max_le_of_forall ?_
  intro x hx
  have hx' : x ∈ insert a u := Finset.mem_def.2 hx
  rcases Finset.mem_insert.mp hx' with rfl | hu
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (le_finsetMaxDepth_of_mem hu) (Nat.le_max_right _ _)

/-- Prop 2.3(ii) via insert-first on `v`. -/
theorem LamConDepth_funion_of_entSet (M : ℕ)
    (ihIns : ∀ u t, Nat.max (finsetMaxDepth u) (rawDepth t) < M →
      LamEntDepth A u t → LamConDepth A (insert t u))
    {u v : Finset (RawLamToken α)}
    (hu : LamConDepth A u)
    (hEnt : ∀ t ∈ v, LamEntDepth A u t)
    (hbound : ∀ t ∈ v, Nat.max (finsetMaxDepth u) (rawDepth t) < M) :
    LamConDepth A (u ∪' v) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  suffices ∀ (v u : Finset (RawLamToken α)),
      LamConDepth A u →
      (∀ t ∈ v, LamEntDepth A u t) →
      (∀ t ∈ v, Nat.max (finsetMaxDepth u) (rawDepth t) < M) →
      LamConDepth A (u ∪' v) from
    this v u hu hEnt hbound
  intro v
  induction v using Finset.induction_on with
  | empty =>
    intro u hu _ _
    simpa [funion_empty_right_lam] using hu
  | insert a t ha ih =>
    intro u hu hEnt hbound
    have mem_a : a ∈ insert a t := Finset.mem_insert_self a t
    have han : Nat.max (finsetMaxDepth u) (rawDepth a) < M := hbound a mem_a
    have hEnt_a : LamEntDepth A u a := hEnt a mem_a
    have hu_ins : LamConDepth A (insert a u) := ihIns u a han hEnt_a
    have hEnt_t : ∀ x ∈ t, LamEntDepth A (insert a u) x := by
      intro x hx
      exact LamEntDepth_weaken_insert A hu_ins
        (hEnt x (Finset.mem_insert_of_mem hx)) hEnt_a
    have hbound_t : ∀ x ∈ t, Nat.max (finsetMaxDepth (insert a u)) (rawDepth x) < M := by
      intro x hx
      have hxu : Nat.max (finsetMaxDepth u) (rawDepth x) < M :=
        hbound x (Finset.mem_insert_of_mem hx)
      have hDi := finsetMaxDepth_insert_le u a
      have h1 : Nat.max (finsetMaxDepth (insert a u)) (rawDepth x) ≤
          Nat.max (Nat.max (rawDepth a) (finsetMaxDepth u)) (rawDepth x) :=
        max_le_max_nat hDi le_rfl
      refine Nat.lt_of_le_of_lt h1 ?_
      have h2 : Nat.max (Nat.max (rawDepth a) (finsetMaxDepth u)) (rawDepth x) =
          Nat.max (rawDepth a) (Nat.max (finsetMaxDepth u) (rawDepth x)) := by
        ac_rfl
      rw [h2]
      exact Nat.max_lt.2 ⟨Nat.lt_of_le_of_lt (Nat.le_max_right _ _) han, hxu⟩
    have hunion : LamConDepth A (insert a u ∪' t) :=
      ih (insert a u) hu_ins hEnt_t hbound_t
    have heq : insert a u ∪' t = u ∪' insert a t := by
      ext x
      constructor
      · intro hx
        rcases mem_funion.1 hx with h | h
        · rcases Finset.mem_insert.mp h with rfl | hu'
          · exact mem_funion.2 (Or.inr (Finset.mem_insert_self _ _))
          · exact mem_funion.2 (Or.inl hu')
        · exact mem_funion.2 (Or.inr (Finset.mem_insert_of_mem h))
      · intro hx
        rcases mem_funion.1 hx with hu' | h
        · exact mem_funion.2 (Or.inl (Finset.mem_insert_of_mem hu'))
        · rcases Finset.mem_insert.mp h with rfl | ht'
          · exact mem_funion.2 (Or.inl (Finset.mem_insert_self _ _))
          · exact mem_funion.2 (Or.inr ht')
    rwa [heq] at hunion

private theorem funion_assoc_lam (a b c : Finset (RawLamToken α)) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inr h)))
      · exact mem_funion.mpr (Or.inr h)

private theorem funion_comm_lam (a b : Finset (RawLamToken α)) : a ∪' b = b ∪' a := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

private theorem finsetMaxDepth_funion_le (u v : Finset (RawLamToken α)) :
    finsetMaxDepth (u ∪' v) ≤ Nat.max (finsetMaxDepth u) (finsetMaxDepth v) := by
  refine foldr_max_le_of_forall ?_
  intro t ht
  have ht' : t ∈ u ∪' v := Finset.mem_def.2 ht
  rcases mem_funion.1 ht' with hu | hv
  · exact Nat.le_trans (le_finsetMaxDepth_of_mem hu) (Nat.le_max_left _ _)
  · exact Nat.le_trans (le_finsetMaxDepth_of_mem hv) (Nat.le_max_right _ _)

/-- Prop 2.1(iii): inserting an entailed token preserves depth-Con. -/
theorem LamConDepth_insert_of_ent {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEntDepth A u t) : LamConDepth A (insert t u) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  suffices ∀ M u t, Nat.max (finsetMaxDepth u) (rawDepth t) = M →
      LamEntDepth A u t → LamConDepth A (insert t u) from
    this _ _ _ rfl ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u t hM ht
    have ihIns : ∀ u' t', Nat.max (finsetMaxDepth u') (rawDepth t') < M →
        LamEntDepth A u' t' → LamConDepth A (insert t' u') :=
      fun u' t' hlt hEnt => ih _ hlt u' t' rfl hEnt
    match t with
    | .bot => exact LamConDepth_insert_bot A (LamEntDepth_con A ht)
    | .atom x => exact LamConDepth_insert_atom A ht
    | .funTok xs ys =>
      cases ht with
      | @funTok u xs ys s hu hA hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
        have hF' : lamFunFinset (insert (.funTok xs ys) u) ≠ ∅ := by
          rw [lamFunFinset_insert_funTok]
          exact Finset.insert_ne_empty _ _
        refine (LamConDepth_of_fun_nonempty A hF').2 ⟨?_, ?_, ?_⟩
        · rw [lamAtomFinset_insert_funTok]; exact hA
        · intro p hp
          rw [lamFunFinset_insert_funTok] at hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact ⟨hConIn, hConOut⟩
          · exact ((LamConDepth_of_fun_nonempty A hWorld).1 hu).2.1 p hp
        · intro sel hsel hIn
          if hp : (xs, ys) ∈ sel then
            let t' := sel.filter (· ≠ (xs, ys))
            have ht_eq : insert (xs, ys) t' = sel := insert_filter_ne_lam hp
            have ht'sub : t' ⊆ lamFunFinset u :=
              filter_ne_subset_of_subset_insert_lam (by
                intro q hq; have := hsel hq; rwa [lamFunFinset_insert_funTok] at this)
            have hin' : LamConDepth A (listToFinset xs ∪' lamInputUnion t') := by
              rwa [← ht_eq, lamInputUnion_insert] at hIn
            have hsub : s ∪' t' ⊆ lamFunFinset u :=
              funion_subset_iff.mpr ⟨hs, ht'sub⟩
            have hEnt_in_s : ∀ z ∈ lamInputUnion s,
                LamEntDepth A (listToFinset xs) z := by
              intro z hz
              rcases (mem_lamInputUnion).1 hz with ⟨p, hp', hz'⟩
              exact hEntIn p hp' z hz'
            have hEnt_big : ∀ z ∈ lamInputUnion s,
                LamEntDepth A (listToFinset xs ∪' lamInputUnion t') z := by
              intro z hz
              have hzx := hEnt_in_s z hz
              have hsubxs : listToFinset xs ⊆ listToFinset xs ∪' lamInputUnion t' :=
                subset_funion_left _ _
              cases decidableEq_finset
                  (lamFunFinset (listToFinset xs ∪' lamInputUnion t')) ∅ with
              | isFalse hFn =>
                have hAv := ((LamConDepth_of_fun_nonempty A hFn).1 hin').1
                exact LamEntDepth_weaken_fun A hsubxs hin' hAv hzx
              | isTrue hFhin =>
                match z with
                | .bot => exact LamEntDepth.bot hin'
                | .atom x =>
                  exact LamEntDepth_weaken_atom A hsubxs hin' hFhin hzx
                | .funTok xs1 ys1 =>
                  cases decidableEq_finset (lamFunFinset (listToFinset xs)) ∅ with
                  | isTrue hxsF =>
                    have hNoFun : lamFunFinset (lamInputUnion s) = ∅ := hInCompat hxsF
                    have hzmem : .funTok xs1 ys1 ∈ lamInputUnion s := hz
                    have : (xs1, ys1) ∈ lamFunFinset (lamInputUnion s) :=
                      mem_lamFunFinset.2 hzmem
                    rw [hNoFun] at this
                    exact False.elim (Finset.notMem_empty _ this)
                  | isFalse hxsF =>
                    have : lamFunFinset (listToFinset xs ∪' lamInputUnion t') ≠ ∅ := by
                      intro h
                      have : lamFunFinset (listToFinset xs) = ∅ :=
                        Finset.Subset.antisymm
                          (fun p hp => by
                            have hp' : p ∈ lamFunFinset
                                (listToFinset xs ∪' lamInputUnion t') := by
                              rw [lamFunFinset_funion]
                              exact mem_funion.2 (Or.inl hp)
                            rw [h] at hp'; exact False.elim (Finset.notMem_empty p hp'))
                          (Finset.empty_subset _)
                      exact hxsF this
                    exact False.elim (this hFhin)
            have hDt : rawDepth (.funTok xs ys) ≤ M := by
              rw [← hM]; exact Nat.le_max_right _ _
            have hDu : finsetMaxDepth u ≤ M := by
              rw [← hM]; exact Nat.le_max_left _ _
            have hxs_lt : finsetMaxDepth (listToFinset xs) < M :=
              Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok xs ys) hDt
            have hys_lt : finsetMaxDepth (listToFinset ys) < M :=
              Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok_out xs ys) hDt
            have bound_in : ∀ z ∈ lamInputUnion s,
                Nat.max (finsetMaxDepth (listToFinset xs ∪' lamInputUnion t'))
                  (rawDepth z) < M := by
              intro z hz
              have hDuBig : finsetMaxDepth (listToFinset xs ∪' lamInputUnion t') < M := by
                have hle := finsetMaxDepth_funion_le (listToFinset xs) (lamInputUnion t')
                refine Nat.lt_of_le_of_lt hle (Nat.max_lt.2 ⟨hxs_lt, ?_⟩)
                by_cases ht'e : t' = ∅
                · rw [ht'e, lamInputUnion_empty]
                  exact Nat.lt_of_le_of_lt (Nat.zero_le _) hxs_lt
                · obtain ⟨q, hq⟩ := Finset.nonempty_of_ne_empty ht'e
                  exact Nat.lt_of_lt_of_le
                    (finsetMaxDepth_inputUnion_lt ht'sub hWorld) hDu
              have hz_lt : rawDepth z < M := by
                rcases (mem_lamInputUnion).1 hz with ⟨p, hp', hz'⟩
                have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp')
                exact Nat.lt_of_lt_of_le
                  (Nat.lt_of_lt_of_le
                    (rawDepth_funTok_gt_left ((mem_listToFinset).1 hz'))
                    (le_finsetMaxDepth_of_mem htok))
                  hDu
              exact Nat.max_lt.2 ⟨hDuBig, hz_lt⟩
            have hbig : LamConDepth A
                ((listToFinset xs ∪' lamInputUnion t') ∪' lamInputUnion s) :=
              LamConDepth_funion_of_entSet A M ihIns hin' hEnt_big bound_in
            have hin_st' : LamConDepth A (lamInputUnion s ∪' lamInputUnion t') := by
              have heq :
                  (listToFinset xs ∪' lamInputUnion t') ∪' lamInputUnion s =
                    listToFinset xs ∪' (lamInputUnion s ∪' lamInputUnion t') := by
                rw [funion_assoc_lam, funion_comm_lam (lamInputUnion t')]
              have hbig' : LamConDepth A
                  (listToFinset xs ∪' (lamInputUnion s ∪' lamInputUnion t')) := by
                rwa [heq] at hbig
              exact LamConDepth_mono A (subset_funion_right _ _) hbig'
            have hin_union : LamConDepth A (lamInputUnion (s ∪' t')) := by
              rwa [lamInputUnion_funion]
            have hout_union : LamConDepth A
                (lamOutputUnion s ∪' lamOutputUnion t') := by
              have hout : LamConDepth A (lamOutputUnion (s ∪' t')) :=
                ((LamConDepth_of_fun_nonempty A hWorld).1 hu).2.2 (s ∪' t') hsub hin_union
              rwa [lamOutputUnion_funion] at hout
            have hEnt_out' : ∀ z ∈ listToFinset ys,
                LamEntDepth A (lamOutputUnion s ∪' lamOutputUnion t') z := by
              intro z hz
              have hzx := hEntOut z hz
              have hsubO : lamOutputUnion s ⊆
                  lamOutputUnion s ∪' lamOutputUnion t' := subset_funion_left _ _
              cases decidableEq_finset
                  (lamFunFinset (lamOutputUnion s ∪' lamOutputUnion t')) ∅ with
              | isFalse hFn =>
                have hAv := ((LamConDepth_of_fun_nonempty A hFn).1 hout_union).1
                exact LamEntDepth_weaken_fun A hsubO hout_union hAv hzx
              | isTrue hFo =>
                match z with
                | .bot => exact LamEntDepth.bot hout_union
                | .atom x =>
                  exact LamEntDepth_weaken_atom A hsubO hout_union hFo hzx
                | .funTok xs1 ys1 =>
                  -- Ent out_s funTok needs fun out_s ≠ ∅, but out_s ⊆ atom-world union
                  cases hzx with
                  | funTok _ _ _ _ hsO hWo _ _ _ =>
                    have hOsF : lamFunFinset (lamOutputUnion s) = ∅ :=
                      Finset.Subset.antisymm
                        (fun p hp => by
                          have : p ∈ lamFunFinset
                              (lamOutputUnion s ∪' lamOutputUnion t') := by
                            rw [lamFunFinset_funion]
                            exact mem_funion.2 (Or.inl hp)
                          rw [hFo] at this
                          exact False.elim (Finset.notMem_empty p this))
                        (Finset.empty_subset _)
                    exact False.elim (hWo hOsF)
            have bound_out : ∀ z ∈ listToFinset ys,
                Nat.max (finsetMaxDepth (lamOutputUnion s ∪' lamOutputUnion t'))
                  (rawDepth z) < M := by
              intro z hz
              have hDuOut : finsetMaxDepth
                  (lamOutputUnion s ∪' lamOutputUnion t') < M := by
                have hle := finsetMaxDepth_funion_le (lamOutputUnion s) (lamOutputUnion t')
                refine Nat.lt_of_le_of_lt hle (Nat.max_lt.2 ⟨?_, ?_⟩)
                · by_cases hs0 : s = ∅
                  · rw [hs0, lamOutputUnion_empty]
                    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hys_lt
                  · exact Nat.lt_of_lt_of_le
                      (finsetMaxDepth_outputUnion_lt hs hWorld) hDu
                · by_cases ht'e : t' = ∅
                  · rw [ht'e, lamOutputUnion_empty]
                    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hys_lt
                  · exact Nat.lt_of_lt_of_le
                      (finsetMaxDepth_outputUnion_lt ht'sub hWorld) hDu
              have hz_lt : rawDepth z < M :=
                Nat.lt_of_lt_of_le
                  (rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)) hDt
              exact Nat.max_lt.2 ⟨hDuOut, hz_lt⟩
            have hfinal : LamConDepth A
                ((lamOutputUnion s ∪' lamOutputUnion t') ∪' listToFinset ys) :=
              LamConDepth_funion_of_entSet A M ihIns hout_union hEnt_out' bound_out
            have hout_t : LamConDepth A
                (listToFinset ys ∪' lamOutputUnion t') := by
              have heq :
                  (lamOutputUnion s ∪' lamOutputUnion t') ∪' listToFinset ys =
                    lamOutputUnion s ∪' (listToFinset ys ∪' lamOutputUnion t') := by
                rw [funion_assoc_lam, funion_comm_lam (lamOutputUnion t')]
              have hfinal' : LamConDepth A
                  (lamOutputUnion s ∪' (listToFinset ys ∪' lamOutputUnion t')) := by
                rwa [heq] at hfinal
              exact LamConDepth_mono A (subset_funion_right _ _) hfinal'
            show LamConDepth A (lamOutputUnion sel)
            rwa [← ht_eq, lamOutputUnion_insert]
          else
            have hsel' : sel ⊆ lamFunFinset u := by
              intro p hp'
              have := hsel hp'
              rw [lamFunFinset_insert_funTok] at this
              rcases Finset.mem_insert.mp this with rfl | h
              · exact False.elim (hp hp')
              · exact h
            exact ((LamConDepth_of_fun_nonempty A hWorld).1 hu).2.2 sel hsel' hIn




/-! ### Scott (8)–(11): `ent_trans` (Def 2.1) -/

/-- Def 2.1 `ent_trans`: cases on the RHS token (Scott’s turnstile advice). -/
theorem LamEntDepth_trans {u v : Finset (RawLamToken α)} {c : RawLamToken α}
    (hv : LamConDepth A v) (hu : LamConDepth A u)
    (hEnts : ∀ t ∈ u, LamEntDepth A v t) (ht : LamEntDepth A u c) :
    LamEntDepth A v c := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  suffices ∀ M u v c,
      Nat.max (finsetMaxDepth v) (Nat.max (finsetMaxDepth u) (rawDepth c)) = M →
      LamConDepth A v → LamConDepth A u →
      (∀ t ∈ u, LamEntDepth A v t) → LamEntDepth A u c → LamEntDepth A v c from
    this _ u v c rfl hv hu hEnts ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u v c hM hv hu hEnts ht
    have hleV : finsetMaxDepth v ≤ M := by rw [← hM]; exact Nat.le_max_left _ _
    have hleU : finsetMaxDepth u ≤ M := by
      rw [← hM]; exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hleC : rawDepth c ≤ M := by
      rw [← hM]; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    -- (8) bot
    match c with
    | .bot => exact LamEntDepth.bot hv
    -- (10) atom
    | .atom x =>
      cases ht with
      | @atom u x hu' hF hne hEnt =>
        obtain ⟨y0, hy0⟩ := Finset.nonempty_of_ne_empty hne
        have hEy0 := hEnts _ (mem_lamAtomFinset.1 hy0)
        have hFv : lamFunFinset v = ∅ := by
          cases hEy0 with
          | atom _ hFv' _ _ => exact hFv'
        have hneV : lamAtomFinset v ≠ ∅ := by
          cases hEy0 with
          | atom _ _ hneV _ => exact hneV
        have hAtomEnt : ∀ y ∈ lamAtomFinset u, A.Ent (lamAtomFinset v) y := by
          intro y hy
          have hEy := hEnts _ (mem_lamAtomFinset.1 hy)
          cases hEy with
          | atom _ _ _ hE => exact hE
        exact LamEntDepth.atom hv hFv hneV
          (A.ent_trans ((LamConDepth_of_fun_empty A hFv).1 hv)
            ((LamConDepth_of_fun_empty A hF).1 hu') hAtomEnt hEnt)
    -- (11) funTok
    | .funTok xs ys =>
      cases ht with
      | @funTok u xs ys s hu' hA hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
        obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hWorld
        have hEp0 := hEnts _ (mem_lamFunFinset.1 hp0)
        have hAv : lamAtomFinset v = ∅ := by
          cases hEp0 with
          | funTok _ hAv' _ _ _ _ _ _ _ => exact hAv'
        have hFv : lamFunFinset v ≠ ∅ := by
          cases hEp0 with
          | funTok _ _ _ _ _ hFv' _ _ _ => exact hFv'
        have hWit : ∀ p ∈ s, ∃ s_p ⊆ lamFunFinset v,
            LamConDepth A (listToFinset p.1) ∧ LamConDepth A (listToFinset p.2) ∧
            (∀ r ∈ s_p, ∀ z ∈ listToFinset r.1, LamEntDepth A (listToFinset p.1) z) ∧
            (∀ z ∈ listToFinset p.2, LamEntDepth A (lamOutputUnion s_p) z) := by
          intro p hp
          have hEp := hEnts _ (mem_lamFunFinset.1 (hs hp))
          cases hEp with
          | @funTok _ _ _ s_p _ _ hCi hCo hs_p _ _ hEi hEo =>
            exact ⟨s_p, hs_p, hCi, hCo, hEi, hEo⟩
        -- Combined witness by Finset.induction_on (choice-free; avoid erase/card)
        have hComb : ∀ (s' : Finset (List (RawLamToken α) × List (RawLamToken α))),
            s' ⊆ s →
            ∃ S ⊆ lamFunFinset v,
              (∀ r ∈ S, ∀ z ∈ listToFinset r.1, LamEntDepth A (listToFinset xs) z) ∧
              (∀ z ∈ lamOutputUnion s', LamEntDepth A (lamOutputUnion S) z) ∧
              LamConDepth A (lamOutputUnion S) := by
          intro s'
          induction s' using Finset.induction_on with
          | empty =>
            intro _
            refine ⟨(∅ : Finset (List (RawLamToken α) × List (RawLamToken α))),
              Finset.empty_subset _, ?_, ?_, ?_⟩
            · intro _ hr; exact False.elim (Finset.notMem_empty _ hr)
            · intro z hz
              rw [lamOutputUnion_empty] at hz
              exact False.elim (Finset.notMem_empty z hz)
            · rw [lamOutputUnion_empty]; exact LamConDepth_empty A
          | insert q sR hq ihS =>
            intro hs'
            have hsR : sR ⊆ s := fun p hp => hs' (Finset.mem_insert_of_mem hp)
            have hqS : q ∈ s := hs' (Finset.mem_insert_self q sR)
            obtain ⟨S', hS'sub, hS'in, hS'out, hConS'⟩ := ihS hsR
            obtain ⟨Sq, hSqsub, hConQIn, hConQOut, hSqin, hSqout⟩ := hWit q hqS
            have hSsub : S' ∪' Sq ⊆ lamFunFinset v :=
              funion_subset_iff.mpr ⟨hS'sub, hSqsub⟩
            have hEntAll : ∀ t ∈ lamInputUnion (S' ∪' Sq),
                LamEntDepth A (listToFinset xs) t := by
              intro t ht
              rcases (mem_lamInputUnion).1 ht with ⟨r, hr, ht'⟩
              rcases mem_funion.1 hr with hr | hr
              · exact hS'in r hr t ht'
              · refine ih _ ?_ (listToFinset q.1) (listToFinset xs) t rfl
                  hConIn hConQIn (fun w hw => hEntIn q hqS w hw) (hSqin r hr t ht')
                have htok : .funTok q.1 q.2 ∈ u := mem_lamFunFinset.1 (hs hqS)
                have htokR : .funTok r.1 r.2 ∈ v :=
                  mem_lamFunFinset.1 (hSsub (mem_funion.2 (Or.inr hr)))
                have hzt := rawDepth_funTok_gt_left (v := r.2) ((mem_listToFinset).1 ht')
                have hDq := (finsetMaxDepth_of_mem_funTok htok).1
                have hDxs := finsetMaxDepth_list_lt_funTok xs ys
                exact Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDxs hleC,
                  Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDq hleU,
                    Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le hzt (le_finsetMaxDepth_of_mem htokR))
                      hleV⟩⟩
            have hinU : LamConDepth A (lamInputUnion (S' ∪' Sq)) :=
              LamConDepth_mono A (subset_funion_right _ _)
                (LamConDepth_funion_of_entSet A M
                  (fun _ _ _ hE => LamConDepth_insert_of_ent A hE)
                  hConIn hEntAll (fun t ht => by
                    rcases (mem_lamInputUnion).1 ht with ⟨r, hr, ht'⟩
                    have hDxs := finsetMaxDepth_list_lt_funTok xs ys
                    have htok : .funTok r.1 r.2 ∈ v := mem_lamFunFinset.1 (hSsub hr)
                    exact Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDxs hleC,
                      Nat.lt_of_lt_of_le
                        (Nat.lt_of_lt_of_le
                          (rawDepth_funTok_gt_left (v := r.2) ((mem_listToFinset).1 ht'))
                          (le_finsetMaxDepth_of_mem htok)) hleV⟩))
            have hConU : LamConDepth A (lamOutputUnion (S' ∪' Sq)) :=
              ((LamConDepth_of_fun_nonempty A hFv).1 hv).2.2 (S' ∪' Sq) hSsub hinU
            have hConU' : LamConDepth A (lamOutputUnion S' ∪' lamOutputUnion Sq) := by
              rw [← lamOutputUnion_funion]; exact hConU
            refine ⟨S' ∪' Sq, hSsub, ?_, ?_, hConU⟩
            · intro r hr z hz
              rcases mem_funion.1 hr with hr | hr
              · exact hS'in r hr z hz
              · exact hEntAll _ ((mem_lamInputUnion).2 ⟨r, mem_funion.2 (Or.inr hr), hz⟩)
            · intro z hz
              rw [lamOutputUnion_funion]
              have hz'' : z ∈ listToFinset q.2 ∪' lamOutputUnion sR := by
                rwa [lamOutputUnion_insert] at hz
              rcases mem_funion.1 hz'' with hzQ | hzR
              · have hzx := hSqout z hzQ
                have hsub := subset_funion_right (lamOutputUnion S') (lamOutputUnion Sq)
                cases decidableEq_finset
                    (lamFunFinset (lamOutputUnion S' ∪' lamOutputUnion Sq)) ∅ with
                | isFalse hFn =>
                  exact LamEntDepth_weaken_fun A hsub hConU'
                    ((LamConDepth_of_fun_nonempty A hFn).1 hConU').1 hzx
                | isTrue hFo =>
                  match z with
                  | .bot => exact LamEntDepth.bot hConU'
                  | .atom _ =>
                    exact LamEntDepth_weaken_atom A hsub hConU' hFo hzx
                  | .funTok _ _ =>
                    cases hzx with
                    | funTok _ _ _ _ _ hWo _ _ _ =>
                      exact False.elim (hWo (Finset.Subset.antisymm
                        (fun p hp => by
                          have : p ∈ lamFunFinset
                              (lamOutputUnion S' ∪' lamOutputUnion Sq) := by
                            rw [lamFunFinset_funion]
                            exact mem_funion.2 (Or.inr hp)
                          exact False.elim (Finset.notMem_empty p (hFo ▸ this)))
                        (Finset.empty_subset _)))
              · have hzx := hS'out z hzR
                have hsub := subset_funion_left (lamOutputUnion S') (lamOutputUnion Sq)
                cases decidableEq_finset
                    (lamFunFinset (lamOutputUnion S' ∪' lamOutputUnion Sq)) ∅ with
                | isFalse hFn =>
                  exact LamEntDepth_weaken_fun A hsub hConU'
                    ((LamConDepth_of_fun_nonempty A hFn).1 hConU').1 hzx
                | isTrue hFo =>
                  match z with
                  | .bot => exact LamEntDepth.bot hConU'
                  | .atom _ =>
                    exact LamEntDepth_weaken_atom A hsub hConU' hFo hzx
                  | .funTok _ _ =>
                    cases hzx with
                    | funTok _ _ _ _ _ hWo _ _ _ =>
                      exact False.elim (hWo (Finset.Subset.antisymm
                        (fun p hp => by
                          have : p ∈ lamFunFinset
                              (lamOutputUnion S' ∪' lamOutputUnion Sq) := by
                            rw [lamFunFinset_funion]
                            exact mem_funion.2 (Or.inl hp)
                          exact False.elim (Finset.notMem_empty p (hFo ▸ this)))
                        (Finset.empty_subset _)))
        obtain ⟨S, hSsub, hSin, hSoutS, hConS⟩ :=
          hComb s (Finset.Subset.refl _)
        have hConOutS : LamConDepth A (lamOutputUnion s) :=
          ((LamConDepth_of_fun_nonempty A hWorld).1 hu').2.2 s hs
            (LamConDepth_mono A (subset_funion_right _ _)
              (LamConDepth_funion_of_entSet A M
                (fun _ _ _ hE => LamConDepth_insert_of_ent A hE)
                hConIn
                (fun t ht => by
                  rcases (mem_lamInputUnion).1 ht with ⟨p, hp, ht'⟩
                  exact hEntIn p hp t ht')
                (fun t ht => by
                  rcases (mem_lamInputUnion).1 ht with ⟨p, hp, ht'⟩
                  have hDxs := finsetMaxDepth_list_lt_funTok xs ys
                  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
                  exact Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDxs hleC,
                    Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le
                        (rawDepth_funTok_gt_left ((mem_listToFinset).1 ht'))
                        (le_finsetMaxDepth_of_mem htok)) hleU⟩)))
        have hSout : ∀ z ∈ listToFinset ys, LamEntDepth A (lamOutputUnion S) z := by
          intro z hz
          refine ih _ ?_ (lamOutputUnion s) (lamOutputUnion S) z rfl
            hConS hConOutS (fun t ht => hSoutS t ht) (hEntOut z hz)
          exact Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le (finsetMaxDepth_outputUnion_lt hSsub hFv) hleV,
            Nat.max_lt.2 ⟨
              Nat.lt_of_lt_of_le (finsetMaxDepth_outputUnion_lt hs hWorld) hleU,
              Nat.lt_of_lt_of_le
                (rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)) hleC⟩⟩
        have hInCompat' : lamFunFinset (listToFinset xs) = ∅ →
            lamFunFinset (lamInputUnion S) = ∅ := by
          intro hxsF
          ext p
          constructor
          · intro hp
            have hmem : .funTok p.1 p.2 ∈ lamInputUnion S := mem_lamFunFinset.1 hp
            rcases (mem_lamInputUnion).1 hmem with ⟨r, hr, hr'⟩
            cases hSin r hr _ hr' with
            | funTok _ _ _ _ _ hWx _ _ _ => exact False.elim (hWx hxsF)
          · intro hp; exact False.elim (Finset.notMem_empty _ hp)
        exact LamEntDepth.funTok hv hAv hConIn hConOut hSsub hFv hInCompat' hSin hSout

/-! ### Phase B — `lambdaSystem` (Def 2.1) on `LamConDepth` -/

/-- Well-formed tokens under depth Con (Scott (1)–(3) for the InfoSys instance).
Early staged `IsLamToken` / `LamToken` remain scaffolding only. -/
def IsLamWF : RawLamToken α → Prop
  | .bot | .atom _ => True
  | .funTok xs ys => LamConDepth A (listToFinset xs) ∧ LamConDepth A (listToFinset ys)

/-- Carrier of `lambdaSystem`. -/
def LamDToken : Type _ := { t : RawLamToken α // IsLamWF A t }

instance : DecidableEq (LamDToken A) := Subtype.instDecidableEq

def lamDBot : LamDToken A := ⟨.bot, trivial⟩

def lamDForget (t : LamDToken A) : RawLamToken α := t.val

private def lamDForgetInsert :
    LamDToken A → Finset (RawLamToken α) → Finset (RawLamToken α) :=
  fun t => insert (lamDForget A t)

private instance : LeftCommutative (lamDForgetInsert (A := A)) :=
  ⟨fun p q s => insert_comm' (lamDForget A p) (lamDForget A q) s⟩

def lamDForgetFinset (u : Finset (LamDToken A)) : Finset (RawLamToken α) :=
  Multiset.foldr (lamDForgetInsert (A := A)) ∅ u.1

private theorem mem_foldr_lamDForget (s : Multiset (LamDToken A)) (t : RawLamToken α) :
    t ∈ Multiset.foldr (lamDForgetInsert (A := A)) ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, lamDForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_lamDForgetFinset {u : Finset (LamDToken A)} {t : RawLamToken α} :
    t ∈ lamDForgetFinset A u ↔ ∃ p ∈ u, p.val = t := by
  simpa [lamDForgetFinset] using mem_foldr_lamDForget A u.1 t

theorem lamDForgetFinset_singleton (p : LamDToken A) :
    lamDForgetFinset A {p} = {p.val} := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, hq'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this; exact Finset.mem_singleton.mpr hq'.symm
  · intro ht
    exact (mem_lamDForgetFinset A).2
      ⟨p, Finset.mem_singleton_self p, (Finset.mem_singleton.mp ht).symm⟩

theorem lamDForgetFinset_insert (u : Finset (LamDToken A)) (p : LamDToken A) :
    lamDForgetFinset A (insert p u) = insert p.val (lamDForgetFinset A u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_lamDForgetFinset A).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_lamDForgetFinset A).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, rfl⟩
      exact (mem_lamDForgetFinset A).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

theorem lamDForgetFinset_mono {u v : Finset (LamDToken A)} (h : v ⊆ u) :
    lamDForgetFinset A v ⊆ lamDForgetFinset A u := by
  intro t ht
  rcases (mem_lamDForgetFinset A).1 ht with ⟨p, hp, rfl⟩
  exact (mem_lamDForgetFinset A).2 ⟨p, h hp, rfl⟩

/-- Singleton funTok is Con when components are (Scott (7) on a singleton). -/
theorem LamConDepth_singleton_funTok (xs ys : List (RawLamToken α))
    (hxs : LamConDepth A (listToFinset xs)) (hys : LamConDepth A (listToFinset ys)) :
    LamConDepth A ({.funTok xs ys} : Finset (RawLamToken α)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.funTok xs ys} : Finset (RawLamToken α)) = {(xs, ys)} :=
    lamFunFinset_singleton_funTok xs ys
  have hA : lamAtomFinset ({.funTok xs ys} : Finset (RawLamToken α)) = ∅ :=
    lamAtomFinset_singleton_funTok xs ys
  have hne : lamFunFinset ({.funTok xs ys} : Finset (RawLamToken α)) ≠ ∅ := by
    rw [hF]; exact Finset.singleton_ne_empty _
  refine (LamConDepth_of_fun_nonempty A hne).2 ⟨hA, ?_, ?_⟩
  · intro p hp
    have : p = (xs, ys) := Finset.mem_singleton.mp (hF ▸ hp)
    subst this; exact ⟨hxs, hys⟩
  · intro s hs hIn
    rw [hF] at hs
    by_cases hmem : (xs, ys) ∈ s
    · have hsin : s = {(xs, ys)} := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (hs hp))
        · intro hp
          have : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst this; exact hmem
      subst hsin
      rw [lamOutputUnion_singleton]
      exact hys
    · have hempty : s = ∅ := by
        ext p
        constructor
        · intro hp
          exact False.elim (hmem (by
            have : p = (xs, ys) := Finset.mem_singleton.mp (hs hp)
            subst this; exact hp))
        · intro hp; exact False.elim (Finset.notMem_empty p hp)
      subst hempty
      rw [lamOutputUnion_empty]
      exact LamConDepth_empty A

theorem IsLamWF_of_mem {u : Finset (RawLamToken α)} (hu : LamConDepth A u)
    {t : RawLamToken α} (ht : t ∈ u) : IsLamWF A t := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  match t with
  | .bot | .atom _ => trivial
  | .funTok xs ys =>
    have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
    by_cases hF : lamFunFinset u = ∅
    · exact False.elim (Finset.notMem_empty _ (hF ▸ hmem))
    · exact ((LamConDepth_of_fun_nonempty A hF).1 hu).2.1 _ hmem

/-- Bundled consistency on `LamDToken` finsets. -/
def LamDCon (u : Finset (LamDToken A)) : Prop :=
  LamConDepth A (lamDForgetFinset A u)

/-- Bundled entailment on `LamDToken`. -/
def LamDEnt (u : Finset (LamDToken A)) (p : LamDToken A) : Prop :=
  LamEntDepth A (lamDForgetFinset A u) p.val

theorem LamDCon_subset {u v : Finset (LamDToken A)}
    (hu : LamDCon A u) (hv : v ⊆ u) : LamDCon A v :=
  LamConDepth_mono A (lamDForgetFinset_mono A hv) hu

theorem LamDCon_singleton (p : LamDToken A) : LamDCon A {p} := by
  rw [LamDCon, lamDForgetFinset_singleton]
  match p.val, p.property with
  | .bot, _ => exact LamConDepth_singleton_bot A
  | .atom x, _ => exact LamConDepth_singleton_atom A x
  | .funTok xs ys, ⟨hxs, hys⟩ => exact LamConDepth_singleton_funTok A xs ys hxs hys

theorem LamDEnt_bot {u : Finset (LamDToken A)} (hu : LamDCon A u) :
    LamDEnt A u (lamDBot A) :=
  LamEntDepth.bot hu

theorem LamDEnt_of_mem {u : Finset (LamDToken A)} {p : LamDToken A}
    (hu : LamDCon A u) (hp : p ∈ u) : LamDEnt A u p :=
  LamEntDepth_of_mem A hu ((mem_lamDForgetFinset A).2 ⟨p, hp, rfl⟩)

theorem LamDCon_insert_of_ent {u : Finset (LamDToken A)} {p : LamDToken A}
    (ht : LamDEnt A u p) : LamDCon A (insert p u) := by
  rw [LamDCon, lamDForgetFinset_insert]
  exact LamConDepth_insert_of_ent A ht

theorem LamDEnt_trans {u v : Finset (LamDToken A)} {c : LamDToken A}
    (hv : LamDCon A v) (hu : LamDCon A u)
    (hEnts : ∀ t ∈ u, LamDEnt A v t) (ht : LamDEnt A u c) :
    LamDEnt A v c :=
  LamEntDepth_trans A hv hu
    (fun t ht' => by
      rcases (mem_lamDForgetFinset A).1 ht' with ⟨p, hp, rfl⟩
      exact hEnts p hp)
    ht

/-- **Definition 2.1 packaging.** The λ-calculus information system `D`. -/
def lambdaSystem : InfoSys (LamDToken A) where
  bot := lamDBot A
  Con := {u | LamDCon A u}
  Ent := LamDEnt A
  con_subset := fun hu hv => LamDCon_subset A hu hv
  con_sing := LamDCon_singleton A
  ent_con := fun h => LamDCon_insert_of_ent A h
  ent_bot := fun hu => LamDEnt_bot A hu
  ent_refl := fun hu hp => LamDEnt_of_mem A hu hp
  ent_trans := fun hv hu hEnts hEntc => LamDEnt_trans A hv hu hEnts hEntc

/-! ### Phase C — domain equation `D ≅ A + (D → D)` -/

/-- Lift a raw Con set to a finset of depth-WF tokens. -/
def listToLamDFinset :
    (xs : List (RawLamToken α)) →
      (∀ t ∈ xs, IsLamWF A t) → Finset (LamDToken A)
  | [], _ => ∅
  | t :: ts, h =>
      insert ⟨t, h t List.mem_cons_self⟩
        (listToLamDFinset ts fun w hw => h w (List.mem_cons_of_mem t hw))

theorem mem_listToLamDFinset {xs : List (RawLamToken α)}
    {h : ∀ t ∈ xs, IsLamWF A t} {p : LamDToken A} :
    p ∈ listToLamDFinset A xs h ↔ p.val ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro hp; exact False.elim (Finset.notMem_empty _ hp)
    · intro hp; cases hp
  | cons t ts ih =>
    constructor
    · intro hp
      rcases Finset.mem_insert.mp hp with hp | hp
      · subst hp; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.1 hp)
    · intro hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih.2 hp)

theorem lamDForget_listToLamDFinset (xs : List (RawLamToken α))
    (h : ∀ t ∈ xs, IsLamWF A t) :
    lamDForgetFinset A (listToLamDFinset A xs h) = listToFinset xs := by
  ext t
  rw [mem_lamDForgetFinset, mem_listToFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_listToLamDFinset A).1 hp
  · intro ht
    let p : LamDToken A := ⟨t, h t ht⟩
    exact ⟨p, (mem_listToLamDFinset A).2 ht, rfl⟩

theorem LamDCon_listToLamDFinset (xs : List (RawLamToken α))
    (hCon : LamConDepth A (listToFinset xs)) :
    LamDCon A (listToLamDFinset A xs fun _t ht =>
      IsLamWF_of_mem A hCon ((mem_listToFinset).2 ht)) := by
  rw [LamDCon, lamDForget_listToLamDFinset]
  exact hCon

/-- Unfold a λ-token into the sum-of-function-space carrier (Scott’s matching). -/
def lamUnfold (t : LamDToken A) :
    SumToken α (FunToken (lambdaSystem A) (lambdaSystem A)) :=
  match t with
  | ⟨.bot, _⟩ => .bot
  | ⟨.atom x, _⟩ => .left x
  | ⟨.funTok xs ys, ⟨hxs, hys⟩⟩ =>
      let u := listToLamDFinset A xs fun _w hw =>
        IsLamWF_of_mem A hxs ((mem_listToFinset).2 hw)
      let v := listToLamDFinset A ys fun _w hw =>
        IsLamWF_of_mem A hys ((mem_listToFinset).2 hw)
      .right ⟨(u, v), ⟨LamDCon_listToLamDFinset A xs hxs,
        LamDCon_listToLamDFinset A ys hys⟩⟩

/-- Right-hand side of the domain equation: `A + (D → D)`. -/
def lamRhs : InfoSys (SumToken α (FunToken (lambdaSystem A) (lambdaSystem A))) :=
  sumSystem A (functionSystem (lambdaSystem A) (lambdaSystem A))
end InfoSys
end DomainTheory.InformationSystems
