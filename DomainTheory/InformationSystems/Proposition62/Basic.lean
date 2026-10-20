/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55

@[expose] public section

/-!
# Proposition 6.2 — product projections and pairing

**Scott 1982, Proposition 6.2.** Approximable `fst`, `snd`, and unique pairing
`⟨f, g⟩` with `fst ∘ ⟨f, g⟩ = f` and `snd ∘ ⟨f, g⟩ = g`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

/-- Left-tagged product token `(X, Δ_B)`. -/
def mkLeft (x : α) : ProdToken A B :=
  ⟨(x, B.bot), Or.inr rfl⟩

/-- Right-tagged product token `(Δ_A, Y)`. -/
def mkRight (y : β) : ProdToken A B :=
  ⟨(A.bot, y), Or.inl rfl⟩

private instance instLeftCommutativeMkLeftInsert :
    LeftCommutative fun x : α =>
      (insert (mkLeft A B x) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkLeft A B x) (mkLeft A B y) s⟩

private instance instLeftCommutativeMkRightInsert :
    LeftCommutative fun y : β =>
      (insert (mkRight A B y) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkRight A B x) (mkRight A B y) s⟩

/-- Embed a finite set of `A`-tokens as left product tokens. -/
def liftLeft (v : Finset α) : Finset (ProdToken A B) :=
  Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) v.1

/-- Embed a finite set of `B`-tokens as right product tokens. -/
def liftRight (w : Finset β) : Finset (ProdToken A B) :=
  Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) w.1

theorem mem_foldr_liftLeft (s : Multiset α) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ x ∈ s, p = mkLeft A B x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

theorem mem_foldr_liftRight (s : Multiset β) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ y ∈ s, p = mkRight A B y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hy, _⟩
      exact False.elim (by cases hy)
  · intro y t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨z, hz, hp⟩)
      · exact ⟨y, Or.inl rfl, hp⟩
      · exact ⟨z, Or.inr hz, hp⟩
    · rintro ⟨z, hz, hp⟩
      rcases hz with rfl | hz
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, hp⟩
theorem ProdCon_empty : ProdCon A B (∅ : Finset (ProdToken A B)) :=
  ⟨by rw [fstFinset_empty]; exact A.con_empty,
    by rw [sndFinset_empty]; exact B.con_empty⟩

/-- Product entailment of a set projects to component entailment on `fst`. -/
theorem entSet_fst_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    A.EntSet (fstFinset A B u) (fstFinset A B v) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.1 hbot

/-- Product entailment of a set projects to component entailment on `snd`. -/
theorem entSet_snd_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    B.EntSet (sndFinset A B u) (sndFinset A B v) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.2 hbot

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.2(1).** Approximable first projection. -/
def fstMap : ApproximableMap (productSystem A B) A where
  rel u v := u ∈ (productSystem A B).Con ∧ v ∈ A.Con ∧ A.EntSet (fstFinset A B u) v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, A.con_empty, by
    rw [fstFinset_empty]; exact A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, hv, huv⟩ ⟨_, hv', huv'⟩
    have hEnt : A.EntSet (fstFinset A B u) (v ∪' v') :=
      proposition_2_3_vi (sys := A) huv huv'
    have hBig : fstFinset A B u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) hu.1 hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu'.1 hv
      (proposition_2_3_iv A hu'.1 hu.1 (entSet_fst_of_prodEntSet A B hEntu) huv) hEntv

/-- **Proposition 6.2(2).** Approximable second projection. -/
def sndMap : ApproximableMap (productSystem A B) B where
  rel u w := u ∈ (productSystem A B).Con ∧ w ∈ B.Con ∧ B.EntSet (sndFinset A B u) w
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, B.con_empty, by
    rw [sndFinset_empty]; exact B.entSet_empty ∅⟩
  union_right := by
    rintro u w w' ⟨hu, hw, huw⟩ ⟨_, hw', huw'⟩
    have hEnt : B.EntSet (sndFinset A B u) (w ∪' w') :=
      proposition_2_3_vi (sys := B) huw huw'
    have hBig : sndFinset A B u ∪' (w ∪' w') ∈ B.Con :=
      proposition_2_3_ii (sys := B) hu.2 hEnt
    have hCon : w ∪' w' ∈ B.Con :=
      B.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' w w' ⟨hu, hw, huw⟩ hEntu hEntw hu' hw'
    refine ⟨hu', hw', ?_⟩
    exact proposition_2_3_iv B hu'.2 hw
      (proposition_2_3_iv B hu'.2 hu.2 (entSet_snd_of_prodEntSet A B hEntu) huw) hEntw

/-- Helper: `g` relates `s` to any subset of `{Δ_B}` once it relates to `∅`. -/
theorem rel_bot_subset {D : InfoSys β} {s : Finset γ} {w : Finset β}
    (g : ApproximableMap C D) (hs : s ∈ C.Con)
    (hg : g.rel s (∅ : Finset β)) (hw : w ⊆ ({D.bot} : Finset β)) :
    g.rel s w := by
  have hwCon : w ∈ D.Con := D.con_subset (D.con_sing D.bot) hw
  have hEnt : D.EntSet (∅ : Finset β) w := by
    intro y hy
    have : y = D.bot := Finset.mem_singleton.mp (hw hy)
    subst this
    exact D.ent_bot D.con_empty
  exact g.mono hg (proposition_2_3_iii C hs) hEnt hs hwCon

/-- Helper: `f` relates `s` to any subset of `{Δ_A}` once it relates to `∅`. -/
theorem rel_bot_subset_left {D : InfoSys α} {s : Finset γ} {v : Finset α}
    (f : ApproximableMap C D) (hs : s ∈ C.Con)
    (hf : f.rel s (∅ : Finset α)) (hv : v ⊆ ({D.bot} : Finset α)) :
    f.rel s v := by
  have hvCon : v ∈ D.Con := D.con_subset (D.con_sing D.bot) hv
  have hEnt : D.EntSet (∅ : Finset α) v := by
    intro x hx
    have : x = D.bot := Finset.mem_singleton.mp (hv hx)
    subst this
    exact D.ent_bot D.con_empty
  exact f.mono hf (proposition_2_3_iii C hs) hEnt hs hvCon

/-- **Proposition 6.2(3).** Pairing of approximable maps. -/
def pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    ApproximableMap C (productSystem A B) where
  rel s u := f.rel s (fstFinset A B u) ∧ g.rel s (sndFinset A B u)
  rel_dom h := f.rel_dom h.1
  rel_cod h := ⟨f.rel_cod h.1, g.rel_cod h.2⟩
  empty_rel := by
    rw [fstFinset_empty, sndFinset_empty]
    exact ⟨f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro s u u' ⟨hf, hg⟩ ⟨hf', hg'⟩
    rw [fstFinset_funion A B u u', sndFinset_funion A B u u']
    exact ⟨f.union_right hf hf', g.union_right hg hg'⟩
  mono := by
    rintro s s' u u' ⟨hf, hg⟩ hEnts hEntu hs' hu'
    refine ⟨?_, ?_⟩
    · exact f.mono hf hEnts (entSet_fst_of_prodEntSet A B hEntu) hs' hu'.1
    · exact g.mono hg hEnts (entSet_snd_of_prodEntSet A B hEntu) hs' hu'.2
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
