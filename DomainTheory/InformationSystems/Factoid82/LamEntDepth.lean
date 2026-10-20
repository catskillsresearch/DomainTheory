/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.Factoid82.RawLamToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def listToFinset {β : Type*} [DecidableEq β] : List β → Finset β
  | [] => ∅
  | x :: xs => insert x (listToFinset xs)

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

theorem mem_listToFinset {β : Type*} [DecidableEq β] {x : β} {xs : List β} :
    x ∈ listToFinset xs ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact False.elim (Finset.notMem_empty x h)
    · intro h; cases h
  | cons a as ih =>
    simp only [listToFinset, Finset.mem_insert, List.mem_cons, ih]




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

end InfoSys
end DomainTheory.InformationSystems
