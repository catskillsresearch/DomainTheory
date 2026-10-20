/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition62
public import DomainTheory.InformationSystems.Factoid32

@[expose] public section

/-!
# Theorem 7.2 — function space elements, apply, and curry

**Scott 1982, Theorem 7.2.** Approximable maps `A → B` are exactly the elements of
`|A → B|`. There is approximable `apply : (B → C) × B → C` with `apply(g,y) = g(y)`,
and for each `h : A × B → C` a unique `curry h : A → (B → C)` satisfying
`h = apply ∘ ⟨(curry h) ∘ fst, snd⟩`.

(`A → B` as an `InfoSys` is already Def 7.1 / `functionSystem`.)
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- Consistency of a packaged function-space token. -/
theorem mkFunToken_property (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    u ∈ A.Con ∧ v ∈ B.Con :=
  ⟨hu, hv⟩

/-- Package a consistent pair as a function-space token. -/
def mkFunToken (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    FunToken A B :=
  ⟨(u, v), mkFunToken_property A B u v hu hv⟩

private theorem funion_self (u : Finset α) : u ∪' u = u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h <;> exact h
  · intro hx
    exact mem_funion.mpr (Or.inl hx)

private theorem funion_comm_β (u v : Finset β) : u ∪' v = v ∪' u := by
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

theorem rel_input_output_union (f : ApproximableMap A B)
    (s : Finset (FunToken A B))
    (hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2)
    (hin : funInputUnion A B s ∈ A.Con) :
    f.rel (funInputUnion A B s) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    exact f.empty_rel
  | insert q s' _hq ih =>
    have hrel' : ∀ r ∈ s', f.rel r.val.1 r.val.2 := fun r hr =>
      hrel r (Finset.mem_insert_of_mem hr)
    have hin' : funInputUnion A B s' ∈ A.Con :=
      A.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hrel' hin'
    have hqrel : f.rel q.val.1 q.val.2 := hrel q (Finset.mem_insert_self q s')
    have hinU : q.val.1 ∪' funInputUnion A B s' ∈ A.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_q : A.EntSet (q.val.1 ∪' funInputUnion A B s') q.val.1 :=
      fun x hx => A.ent_refl hinU (subset_funion_left _ _ hx)
    have hEnt_s : A.EntSet (q.val.1 ∪' funInputUnion A B s') (funInputUnion A B s') :=
      fun x hx => A.ent_refl hinU (subset_funion_right _ _ hx)
    have h1 : f.rel (q.val.1 ∪' funInputUnion A B s') q.val.2 :=
      f.mono hqrel hEnt_q (proposition_2_3_iii B q.property.2) hinU q.property.2
    have h2 : f.rel (q.val.1 ∪' funInputUnion A B s') (funOutputUnion A B s') :=
      f.mono ih' hEnt_s (proposition_2_3_iii B (f.rel_cod ih')) hinU (f.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact f.union_right h1 h2

open ApproximableMap

theorem funCon_of_approxMap (f : ApproximableMap A B) (w : Finset (FunToken A B))
    (hw : ∀ p ∈ w, f.rel p.val.1 p.val.2) : FunCon A B w :=
  fun s hs hin =>
    f.rel_cod (rel_input_output_union A B f s (fun q hq => hw q (hs hq)) hin)

/-- Consistency of the token-set of an approximable map. -/
theorem approxMap_toElement_consistent (f : ApproximableMap A B)
    (Y : Finset (FunToken A B))
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2}) :
    Y ∈ (functionSystem A B).Con :=
  funCon_of_approxMap A B f Y fun _ hp => hY (Finset.mem_coe.2 hp)

/-- Deductive closure of the token-set of an approximable map. -/
theorem approxMap_toElement_closed (f : ApproximableMap A B)
    (Y : Finset (FunToken A B)) (p : FunToken A B)
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2})
    (hEnt : (functionSystem A B).Ent Y p) :
    p ∈ {q : FunToken A B | f.rel q.val.1 q.val.2} := by
  obtain ⟨_hCon, s, hs, hEntIn, hEntOut⟩ := hEnt
  have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq =>
    hY (Finset.mem_coe.2 (hs hq))
  have hin_s : funInputUnion A B s ∈ A.Con :=
    A.con_subset
      (proposition_2_3_ii A p.property.1 (entSet_inputUnion_of_ent A B hEntIn))
      (subset_funion_right _ _)
  have hIO := rel_input_output_union A B f s hrel hin_s
  have hU : f.rel p.val.1 (funOutputUnion A B s) :=
    f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
      (proposition_2_3_iii B (f.rel_cod hIO)) p.property.1 (f.rel_cod hIO)
  exact f.mono hU (proposition_2_3_iii A p.property.1) hEntOut p.property.1 p.property.2

/-- **Theorem 7.2.** Approximable map as an element of `|A → B|`. -/
def approxMap_toElement (f : ApproximableMap A B) : (functionSystem A B).Element where
  carrier := {p : FunToken A B | f.rel p.val.1 p.val.2}
  consistent := approxMap_toElement_consistent A B f
  closed := approxMap_toElement_closed A B f

/-- Domain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_dom (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      u ∈ A.Con :=
  fun ⟨hu, _, _⟩ => hu

/-- Codomain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_cod (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      v ∈ B.Con :=
  fun ⟨_, hv, _⟩ => hv

/-- The empty pair is related. -/
theorem element_toApproxMap_empty_rel (x : (functionSystem A B).Element) :
    ∃ (hu : (∅ : Finset α) ∈ A.Con) (hv : (∅ : Finset β) ∈ B.Con),
      mkFunToken A B ∅ ∅ hu hv ∈ x.carrier := by
  refine ⟨A.con_empty, B.con_empty, ?_⟩
  change funBot A B ∈ x.carrier
  exact factoid_3_2 (functionSystem A B) x

/-- Output-union of two related pairs remains related. -/
theorem element_toApproxMap_union_right (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      (∃ (hu : u ∈ A.Con) (hv : v' ∈ B.Con), mkFunToken A B u v' hu hv ∈ x.carrier) →
      ∃ (hu : u ∈ A.Con) (hv : v ∪' v' ∈ B.Con),
        mkFunToken A B u (v ∪' v') hu hv ∈ x.carrier := by
  rintro u v v' ⟨hu, hv, hp⟩ ⟨hu', hv', hq⟩
  have hvU : v ∪' v' ∈ B.Con := by
    have hCon : FunCon A B
        (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) := by
      apply x.consistent
      intro r hr
      rcases Finset.mem_insert.mp (Finset.mem_coe.1 hr) with rfl | hr
      · exact hq
      · have : r = mkFunToken A B u v hu hv := Finset.mem_singleton.mp hr
        subst this
        exact hp
    have hin : funInputUnion A B
        (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) ∈ A.Con := by
      rw [funInputUnion_insert, funInputUnion_singleton]
      change u ∪' u ∈ A.Con
      rw [funion_self]
      exact hu
    have hout := hCon _ (Finset.Subset.refl _) hin
    rw [funOutputUnion_insert, funOutputUnion_singleton, funion_comm_β] at hout
    exact hout
  refine ⟨hu, hvU, ?_⟩
  let p := mkFunToken A B u v hu hv
  let q := mkFunToken A B u v' hu' hv'
  let r := mkFunToken A B u (v ∪' v') hu hvU
  let w : Finset (FunToken A B) := insert q {p}
  have hwsub : (↑w : Set _) ⊆ x.carrier := by
    intro t ht
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 ht) with rfl | ht
    · exact hq
    · have : t = p := Finset.mem_singleton.mp ht
      subst this
      exact hp
  have hEnt : FunEnt A B w r := by
    refine ⟨x.consistent w hwsub, w, Finset.Subset.refl _, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact proposition_2_3_iii A hu'
      · have : t = p := Finset.mem_singleton.mp ht
        subst this
        exact proposition_2_3_iii A hu
    · have houtEq : funOutputUnion A B w = v' ∪' v := by
        change funOutputUnion A B
          (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) = v' ∪' v
        rw [funOutputUnion_insert, funOutputUnion_singleton]
        simp only [mkFunToken]
      rw [houtEq, funion_comm_β]
      exact proposition_2_3_iii B hvU
  exact x.closed w r hwsub hEnt

/-- The recovered relation is monotone for entailment. -/
theorem element_toApproxMap_mono (x : (functionSystem A B).Element) :
    ∀ {u u' : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con →
      ∃ (hu : u' ∈ A.Con) (hv : v' ∈ B.Con),
        mkFunToken A B u' v' hu hv ∈ x.carrier := by
  rintro u u' v v' ⟨hu, hv, hp⟩ hEntu hEntv hu' hv'
  refine ⟨hu', hv', ?_⟩
  let p := mkFunToken A B u v hu hv
  let r := mkFunToken A B u' v' hu' hv'
  have hwsub : (↑({p} : Finset (FunToken A B)) : Set _) ⊆ x.carrier := by
    intro t ht
    have : t = p := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
    subst this
    exact hp
  have hEnt : FunEnt A B {p} r := by
    refine ⟨x.consistent {p} hwsub, {p}, Finset.Subset.refl _, ?_, ?_⟩
    · intro t ht
      have : t = p := Finset.mem_singleton.mp ht
      subst this
      exact hEntu
    · rw [funOutputUnion_singleton]
      exact hEntv
  exact x.closed {p} r hwsub hEnt

/-- **Theorem 7.2.** Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := element_toApproxMap_rel_dom A B x
  rel_cod := element_toApproxMap_rel_cod A B x
  empty_rel := element_toApproxMap_empty_rel A B x
  union_right := element_toApproxMap_union_right A B x
  mono := element_toApproxMap_mono A B x

/-- **Theorem 7.2.** Approximable `apply : (B → C) × B → C`. -/
def applyMap : ApproximableMap (productSystem (functionSystem B C) B) C where
  rel s t :=
    ∃ (hs : ProdCon (functionSystem B C) B s) (ht : t ∈ C.Con),
      FunEnt B C (fstFinset (functionSystem B C) B s)
        (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht)
  rel_dom := fun ⟨hs, _, _⟩ => hs
  rel_cod := fun ⟨_, ht, _⟩ => ht
  empty_rel := by
    have hs : ProdCon (functionSystem B C) B ∅ :=
      ⟨by rw [fstFinset_empty]; exact (functionSystem B C).con_empty,
        by rw [sndFinset_empty]; exact B.con_empty⟩
    refine ⟨hs, C.con_empty, ?_⟩
    have hfst : fstFinset (functionSystem B C) B (∅ : Finset _) = ∅ := fstFinset_empty _ _
    have hsnd : sndFinset (functionSystem B C) B (∅ : Finset _) = ∅ := sndFinset_empty _ _
    simp only [hfst, hsnd]
    exact (functionSystem B C).ent_bot (functionSystem B C).con_empty
  union_right := by
    rintro s t t' ⟨hs, ht, hEntt⟩ ⟨_, ht', hEntt'⟩
    obtain ⟨hw, s1, hs1, hIn1, hOut1⟩ := hEntt
    obtain ⟨_, s2, hs2, hIn2, hOut2⟩ := hEntt'
    have hsub : s1 ∪' s2 ⊆ fstFinset (functionSystem B C) B s :=
      funion_subset_iff.mpr ⟨hs1, hs2⟩
    have hin : funInputUnion B C (s1 ∪' s2) ∈ B.Con := by
      rw [funInputUnion_funion]
      have hEntU : B.EntSet (sndFinset (functionSystem B C) B s)
          (funInputUnion B C s1 ∪' funInputUnion B C s2) :=
        proposition_2_3_vi B
          (entSet_inputUnion_of_ent B C hIn1)
          (entSet_inputUnion_of_ent B C hIn2)
      exact B.con_subset (proposition_2_3_ii B hs.2 hEntU) (subset_funion_right _ _)
    have hout : funOutputUnion B C s1 ∪' funOutputUnion B C s2 ∈ C.Con := by
      have := hw _ hsub hin
      rwa [funOutputUnion_funion] at this
    have htt' : t ∪' t' ∈ C.Con := by
      have hEntt2 : C.EntSet (funOutputUnion B C s1 ∪' funOutputUnion B C s2) (t ∪' t') :=
        proposition_2_3_vi C
          (proposition_2_3_v C (C.con_subset hout (subset_funion_left _ _)) hout
            (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
          (proposition_2_3_v C (C.con_subset hout (subset_funion_right _ _)) hout
            (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
      exact C.con_subset (proposition_2_3_ii C hout hEntt2) (subset_funion_right _ _)
    refine ⟨hs, htt', hw, s1 ∪' s2, hsub, ?_, ?_⟩
    · intro q hq
      rcases mem_funion.mp hq with hq | hq
      · exact hIn1 q hq
      · exact hIn2 q hq
    · rw [funOutputUnion_funion]
      exact proposition_2_3_vi C
        (proposition_2_3_v C (C.con_subset hout (subset_funion_left _ _)) hout
          (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
        (proposition_2_3_v C (C.con_subset hout (subset_funion_right _ _)) hout
          (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
  mono := by
    rintro s s' t t' ⟨hs, ht, hEnt⟩ hEnts hEntt hs' ht'
    refine ⟨hs', ht', ?_⟩
    have hfst := entSet_fst_of_prodEntSet (functionSystem B C) B hEnts
    have hsnd := entSet_snd_of_prodEntSet (functionSystem B C) B hEnts
    have htok :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s)
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) := hEnt
    have hmid :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s')
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) :=
      (functionSystem B C).ent_trans hs'.1 hs.1 (fun y hy => hfst y hy) htok
    obtain ⟨hw', s1, hs1, hIn1, hOut1⟩ := hmid
    have hIn1' : ∀ q ∈ s1, B.EntSet (sndFinset (functionSystem B C) B s') q.val.1 :=
      fun q hq => proposition_2_3_iv B hs'.2 hs.2 hsnd (hIn1 q hq)
    have hin : funInputUnion B C s1 ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hs'.2 (entSet_inputUnion_of_ent B C hIn1'))
        (subset_funion_right _ _)
    have hout : funOutputUnion B C s1 ∈ C.Con := hw' s1 hs1 hin
    refine ⟨hw', s1, hs1, hIn1', ?_⟩
    exact proposition_2_3_iv C hout ht hOut1 hEntt

/-! ## Curry helpers -/

/-- Product token set encoding a pair of consistent sets `(u, v)`. -/
def liftPair (u : Finset α) (v : Finset β) : Finset (ProdToken A B) :=
  liftLeft A B u ∪' liftRight A B v

theorem ProdCon_liftPair {u : Finset α} {v : Finset β}
    (hu : u ∈ A.Con) (hv : v ∈ B.Con) : ProdCon A B (liftPair A B u v) := by
  constructor
  · unfold liftPair
    rw [fstFinset_funion, fstFinset_liftLeft]
    have hEnt : A.EntSet u (fstFinset A B (liftRight A B v)) := fun x hx => by
      have : x = A.bot := Finset.mem_singleton.mp (fstFinset_liftRight A B v hx)
      subst this
      exact A.ent_bot hu
    exact proposition_2_3_ii A hu hEnt
  · unfold liftPair
    rw [sndFinset_funion, sndFinset_liftRight]
    have hEnt : B.EntSet v (sndFinset A B (liftLeft A B u)) := fun y hy => by
      have : y = B.bot := Finset.mem_singleton.mp (sndFinset_liftLeft A B u hy)
      subst this
      exact B.ent_bot hv
    have h := proposition_2_3_ii B hv hEnt
    rwa [funion_comm_β] at h

theorem fstFinset_liftPair (u : Finset α) (v : Finset β) :
    fstFinset A B (liftPair A B u v) =
      u ∪' fstFinset A B (liftRight A B v) := by
  unfold liftPair
  rw [fstFinset_funion, fstFinset_liftLeft]

theorem sndFinset_liftPair (u : Finset α) (v : Finset β) :
    sndFinset A B (liftPair A B u v) =
      sndFinset A B (liftLeft A B u) ∪' v := by
  unfold liftPair
  rw [sndFinset_funion, sndFinset_liftRight]

/-- Product entailment between lifted pairs from component entailments. -/
theorem entSet_liftPair {u u' : Finset α} {v v' : Finset β}
    (hu' : u' ∈ A.Con) (hv' : v' ∈ B.Con)
    (hEntu : A.EntSet u' u) (hEntv : B.EntSet v' v) :
    (productSystem A B).EntSet (liftPair A B u' v') (liftPair A B u v) := by
  intro p hp
  have hCon : ProdCon A B (liftPair A B u' v') := ProdCon_liftPair A B hu' hv'
  unfold liftPair at hp
  rcases mem_funion.mp hp with hp | hp
  · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      have hsub : u' ⊆ fstFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [fstFinset_liftPair]
        exact subset_funion_left _ _ hz
      exact A.ent_trans hCon.1 hu'
        (fun z hz => A.ent_refl hCon.1 (hsub hz)) (hEntu x hx)
    · intro _
      exact B.ent_bot hCon.2
  · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      exact A.ent_bot hCon.1
    · intro _
      have hsub : v' ⊆ sndFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hz
      exact B.ent_trans hCon.2 hv'
        (fun z hz => B.ent_refl hCon.2 (hsub hz)) (hEntv y hy)

/-- Combine pointwise `h`-relations along a finite set of function tokens. -/
theorem rel_of_funTokens (h : ApproximableMap (productSystem A B) C)
    (u : Finset α) (hu : u ∈ A.Con) (t : Finset (FunToken B C))
    (hps : ∀ p ∈ t, h.rel (liftPair A B u p.val.1) p.val.2)
    (hin : funInputUnion B C t ∈ B.Con) :
    h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) := by
  induction t using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    have hdom : liftPair A B u ∅ ∈ (productSystem A B).Con :=
      ProdCon_liftPair A B hu B.con_empty
    exact h.mono h.empty_rel
      ((productSystem A B).entSet_empty _)
      (C.entSet_empty ∅) hdom C.con_empty
  | insert p t' hpnot ih =>
    have hps' : ∀ q ∈ t', h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (Finset.mem_insert_of_mem hq)
    have hin' : funInputUnion B C t' ∈ B.Con :=
      B.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hps' hin'
    have hp : h.rel (liftPair A B u p.val.1) p.val.2 :=
      hps p (Finset.mem_insert_self p t')
    have hinU : p.val.1 ∪' funInputUnion B C t' ∈ B.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_p : B.EntSet (p.val.1 ∪' funInputUnion B C t') p.val.1 :=
      fun y hy => B.ent_refl hinU (subset_funion_left _ _ hy)
    have hEnt_t : B.EntSet (p.val.1 ∪' funInputUnion B C t') (funInputUnion B C t') :=
      fun y hy => B.ent_refl hinU (subset_funion_right _ _ hy)
    have hdomU : liftPair A B u (p.val.1 ∪' funInputUnion B C t') ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hu hinU
    have h1 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t')) p.val.2 :=
      h.mono hp
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_p)
        (proposition_2_3_iii C (h.rel_cod hp)) hdomU (h.rel_cod hp)
    have h2 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t'))
        (funOutputUnion B C t') :=
      h.mono ih'
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_t)
        (proposition_2_3_iii C (h.rel_cod ih')) hdomU (h.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact h.union_right h1 h2

theorem funCon_of_curry_pointwise (h : ApproximableMap (productSystem A B) C)
    {u : Finset α} (hu : u ∈ A.Con) {s : Finset (FunToken B C)}
    (hps : ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2) :
    FunCon B C s :=
  fun t ht hin =>
    h.rel_cod (rel_of_funTokens A B C h u hu t (fun p hp => hps p (ht hp)) hin)

/-- **Theorem 7.2.** Approximable `curry h : A → (B → C)`. -/
def curryMap (h : ApproximableMap (productSystem A B) C) :
    ApproximableMap A (functionSystem B C) where
  rel u s :=
    u ∈ A.Con ∧ ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2
  rel_dom hrel := hrel.1
  rel_cod hrel := funCon_of_curry_pointwise A B C h hrel.1 hrel.2
  empty_rel := ⟨A.con_empty, fun _ hp => False.elim (Finset.notMem_empty _ hp)⟩
  union_right := by
    rintro u s s' ⟨hu, hps⟩ ⟨_, hps'⟩
    refine ⟨hu, ?_⟩
    intro p hp
    rcases mem_funion.mp hp with hp | hp
    · exact hps p hp
    · exact hps' p hp
  mono := by
    rintro u u' s s' ⟨hu, hps⟩ hEntu hEnts hu' hs'
    refine ⟨hu', ?_⟩
    intro p hp
    -- FunEnt s p from EntSet
    have hEntp : FunEnt B C s p := hEnts p hp
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEntp
    have hps_t : ∀ q ∈ t, h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B p.property.1 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h u hu t hps_t hin
    have hmid' : h.rel (liftPair A B u' p.val.1) (funOutputUnion B C t) :=
      h.mono hmid
        (entSet_liftPair A B hu' p.property.1 hEntu
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii C (h.rel_cod hmid))
        (ProdCon_liftPair A B hu' p.property.1) (h.rel_cod hmid)
    exact h.mono hmid'
      (proposition_2_3_iii (productSystem A B) (ProdCon_liftPair A B hu' p.property.1))
      hOut (ProdCon_liftPair A B hu' p.property.1) p.property.2

/-- Product element `⟨x, y⟩` assembled from the two projections. -/
def pairElements (x : A.Element) (y : B.Element) : (productSystem A B).Element where
  carrier := {p : ProdToken A B |
    (p.val.2 = B.bot → p.val.1 ∈ x.carrier) ∧ (p.val.1 = A.bot → p.val.2 ∈ y.carrier)}
  consistent := by
    intro Y hY
    refine ⟨?_, ?_⟩
    · have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).1 hbot
      exact x.consistent _ hsub
    · have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).2 hbot
      exact y.consistent _ hsub
  closed := by
    intro Y p hY hEnt
    obtain ⟨hCon, hL, hR⟩ := hEnt
    refine ⟨?_, ?_⟩
    · intro hbot
      have hEntA : A.Ent (fstFinset A B Y) p.val.1 := hL hbot
      have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).1 hbot'
      exact x.closed _ _ hsub hEntA
    · intro hbot
      have hEntB : B.Ent (sndFinset A B Y) p.val.2 := hR hbot
      have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).2 hbot'
      exact y.closed _ _ hsub hEntB

/-- The uncurrying of `k : A → (B → C)`. -/
def uncurryMap (k : ApproximableMap A (functionSystem B C)) :
    ApproximableMap (productSystem A B) C :=
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B))
end InfoSys
end DomainTheory.InformationSystems
