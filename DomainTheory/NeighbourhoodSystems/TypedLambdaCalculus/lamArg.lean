module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.iterStack
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.numberDomain
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.PartrecLam
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.NatDom (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

def optElem : Option ℕ → N.Element
  | none => N.bot
  | some n => natElem n

abbrev 𝒩 : NeighborhoodSystem (ℕ × ℕ) := iterSys N

def ArgLike (z : 𝒩.Element) : Prop := ∀ j, component z j = N.bot ∨ ∃ k, component z j = natElem k

def argElem {n : ℕ} (a : Fin n → Option ℕ) : 𝒩.Element :=
  ofSeq (fun i => if h : i < n then optElem (a ⟨i, h⟩) else N.bot)

def vecElem {n : ℕ} (v : List.Vector ℕ n) : 𝒩.Element :=
  argElem (fun i => some (v.get i))

structure LamDef {n : ℕ} (φ : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ) : Prop where
  defined : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → φ.toElementMap (vecElem v) = natElem c
  undef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → φ.toElementMap (vecElem v) = N.bot
  strict : ∀ (z : 𝒩.Element), ArgLike z → ∀ i, i < n → component z i = N.bot →
    φ.toElementMap z = N.bot

@[simp] theorem component_argElem {n : ℕ} (a : Fin n → Option ℕ) (i : ℕ) :
    component (argElem a) i = if h : i < n then optElem (a ⟨i, h⟩) else N.bot := by
  rw [argElem, component_ofSeq]

@[simp] theorem component_vecElem {n : ℕ} (v : List.Vector ℕ n) (i : ℕ) :
    component (vecElem v) i = if h : i < n then natElem (v.get ⟨i, h⟩) else N.bot := by
  rw [vecElem, component_argElem]; split <;> rfl

def guard1 (j : ℕ) (φ : ApproximableMap 𝒩 N) : ApproximableMap 𝒩 N :=
  (cond N).comp (paired (zeroMap.comp (projN N j)) (paired φ φ))

def oneArg : ApproximableMap N 𝒩 := (push N).comp (paired (idMap N) (constMap N 𝒩.bot))

def strictGuardN : ℕ → ApproximableMap 𝒩 N → ApproximableMap 𝒩 N
  | 0, φ => φ
  | n + 1, φ => guard1 n (strictGuardN n φ)

def tupleMap : (n : ℕ) → (Fin n → ApproximableMap 𝒩 N) → ApproximableMap 𝒩 𝒩
  | 0, _ => constMap 𝒩 𝒩.bot
  | n + 1, gs => (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ)))

theorem T_bot_eq : (NatDom.T).bot = Truth.botElt :=
  le_antisymm ((NatDom.T).bot_le _) (Truth.botElt_le _)

theorem argElem_argLike {n : ℕ} (a : Fin n → Option ℕ) : ArgLike (argElem a) := by
  intro j
  rw [component_argElem]
  split
  · cases h : a _ with
    | none => exact Or.inl rfl
    | some k => exact Or.inr ⟨k, rfl⟩
  · exact Or.inl rfl

theorem component_argElem_none {n : ℕ} (a : Fin n → Option ℕ) (i : Fin n) (hi : a i = none) :
    component (argElem a) (i : ℕ) = N.bot := by
  rw [component_argElem, dite_eq_left i.isLt, Fin.eta, hi]; rfl

theorem component_bot (i : ℕ) : component (𝒩.bot) i = N.bot := by
  have hbot : (𝒩.bot) = ofSeq (fun _ => N.bot) :=
    le_antisymm (𝒩.bot_le _)
      (le_of_component_le (fun i => by rw [component_ofSeq]; exact N.bot_le _))
  rw [hbot, component_ofSeq]

theorem component_push_succ (x : N.Element) (s : 𝒩.Element) (j : ℕ) :
    component ((push N).toElementMap (pair x s)) (j + 1) = component s j := by
  rw [← component_tail, tail_push]

theorem component_push_zero (x : N.Element) (s : 𝒩.Element) :
    component ((push N).toElementMap (pair x s)) 0 = x := by
  rw [← head_apply, head_push]

theorem component_vecElem_lt {n : ℕ} (v : List.Vector ℕ n) {j : ℕ} (hj : j < n) :
    component (vecElem v) j = natElem (v.get ⟨j, hj⟩) := by
  rw [component_vecElem, dite_eq_left hj]

theorem eq_of_component_eq {z z' : 𝒩.Element}
    (h : ∀ n, component z n = component z' n) : z = z' :=
  le_antisymm (le_of_component_le (fun n => (h n).le))
    (le_of_component_le (fun n => (h n).ge))

theorem guard1_apply (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element) :
    (guard1 j φ).toElementMap z =
      (cond N).toElementMap (pair (zeroMap.toElementMap (component z j))
        (pair (φ.toElementMap z) (φ.toElementMap z))) := by
  rw [guard1, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_projN]

theorem guard1_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : component z j = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rw [guard1_apply, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

theorem guard1_inner_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : component z j = N.bot ∨ ∃ k, component z j = natElem k)
    (h : φ.toElementMap z = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rcases hz with hb | ⟨k, hk⟩
  · exact guard1_bot j φ z hb
  · rw [guard1_apply, hk, h]
    cases k with
    | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
    | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]

theorem guard1_total (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element) {k : ℕ}
    (h : component z j = natElem k) : (guard1 j φ).toElementMap z = φ.toElementMap z := by
  rw [guard1_apply, h]
  cases k with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]

theorem lamDef_coe_val {n : ℕ} {φ : ApproximableMap 𝒩 N} {g : List.Vector ℕ n → ℕ}
    (h : LamDef φ (g : List.Vector ℕ n →. ℕ)) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = natElem (g v) :=
  h.defined v (g v) (by rw [PFun.coe_val]; exact Part.mem_some _)

theorem lamDef_congr {n : ℕ} {φ : ApproximableMap 𝒩 N} {f f' : List.Vector ℕ n →. ℕ}
    (h : ∀ v, f v = f' v) (hf : LamDef φ f) : LamDef φ f' where
  defined v c hc := hf.defined v c (by rw [h v]; exact hc)
  undef v hv := hf.undef v (by rw [h v]; exact hv)
  strict := hf.strict

theorem mem_mOfFn : ∀ {n : ℕ} (p : Fin n → Part ℕ) (w : List.Vector ℕ n),
    w ∈ List.Vector.mOfFn p ↔ ∀ i, w.get i ∈ p i
  | 0, p, w => by
      constructor
      · intro _ i; exact i.elim0
      · intro _
        show w ∈ (pure List.Vector.nil : Part _)
        rw [Part.pure_eq_some, Part.mem_some_iff]
        exact List.Vector.eq_nil w
  | n + 1, p, w => by
      have hmof : List.Vector.mOfFn p
          = (p 0).bind (fun a => (List.Vector.mOfFn fun i => p i.succ).bind
              (fun u => Part.some (a ::ᵥ u))) := by
        simp only [List.Vector.mOfFn, Part.bind_eq_bind, Part.pure_eq_some]
      rw [hmof, Part.mem_bind_iff]
      constructor
      · rintro ⟨a, ha, hrest⟩
        rw [Part.mem_bind_iff] at hrest
        obtain ⟨u, hu, hw⟩ := hrest
        rw [Part.mem_some_iff] at hw
        subst hw
        have hu' := (mem_mOfFn (fun i => p i.succ) u).mp hu
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ha
        · intro k; simpa using hu' k
      · intro hall
        refine ⟨w.head, ?_, ?_⟩
        · have := hall 0; rwa [List.Vector.get_zero] at this
        · rw [Part.mem_bind_iff]
          refine ⟨w.tail, (mem_mOfFn (fun i => p i.succ) w.tail).mpr (fun k => ?_), ?_⟩
          · have h := hall k.succ
            rwa [← List.Vector.get_tail_succ w k] at h
          · rw [Part.mem_some_iff]; exact (List.Vector.cons_head_tail w).symm

theorem oneArg_bot : (oneArg).toElementMap N.bot = 𝒩.bot := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  apply eq_of_component_eq
  intro i
  cases i with
  | zero => rw [component_push_zero, component_bot]
  | succ k => rw [component_push_succ, component_bot, component_bot]

theorem push_natElem_vecElem {n : ℕ} (a : ℕ) (u : List.Vector ℕ n) :
    (push N).toElementMap (pair (natElem a) (vecElem u)) = vecElem (a ::ᵥ u) := by
  apply eq_of_component_eq
  intro j
  cases j with
  | zero =>
    rw [component_push_zero, component_vecElem, dite_eq_left (Nat.succ_pos n)]
    exact congrArg natElem (List.Vector.get_cons_zero a u).symm
  | succ k =>
    rw [component_push_succ, component_vecElem, component_vecElem]
    by_cases hk : k < n
    · rw [dite_eq_left hk, dite_eq_left (show k + 1 < n + 1 by omega)]
      exact congrArg natElem (List.Vector.get_cons_succ a u ⟨k, hk⟩).symm
    · rw [dite_eq_right hk, dite_eq_right (show ¬ k + 1 < n + 1 by omega)]

theorem oneArg_natElem (a : ℕ) :
    (oneArg).toElementMap (natElem a) = vecElem (a ::ᵥ (List.Vector.nil : List.Vector ℕ 0)) := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  rw [show 𝒩.bot = vecElem (List.Vector.nil : List.Vector ℕ 0) from ?_, push_natElem_vecElem]
  exact eq_of_component_eq (fun i => by rw [component_bot, component_vecElem, dite_eq_right (by omega)])

theorem realizer_value {n : ℕ} {φ : ApproximableMap 𝒩 N} {f : List.Vector ℕ n →. ℕ}
    (h : LamDef φ f) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = N.bot ∨ ∃ k, φ.toElementMap (vecElem v) = natElem k := by
  by_cases hd : (f v).Dom
  · exact Or.inr ⟨(f v).get hd, h.defined v _ (Part.get_mem hd)⟩
  · exact Or.inl (h.undef v hd)

theorem strictGuardN_strict (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : ArgLike z) {i : ℕ} (hi : i < n) (hb : component z i = N.bot) :
    (strictGuardN n φ).toElementMap z = N.bot := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    rw [strictGuardN]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact guard1_inner_bot m _ z (hz m) (ih hlt)
    · exact guard1_bot m _ z (heq ▸ hb)

theorem strictGuardN_total (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : ∀ j, j < n → ∃ k, component z j = natElem k) :
    (strictGuardN n φ).toElementMap z = φ.toElementMap z := by
  induction n with
  | zero => rfl
  | succ m ih =>
    obtain ⟨k, hk⟩ := h m (Nat.lt_succ_self m)
    rw [strictGuardN, guard1_total m _ z hk]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))

theorem tupleMap_succ (n : ℕ) (gs : Fin (n + 1) → ApproximableMap 𝒩 N) :
    tupleMap (n + 1) gs = (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ))) := rfl

theorem component_tupleMap : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ) (hi : i < n),
    component ((tupleMap n gs).toElementMap z) i = (gs ⟨i, hi⟩).toElementMap z
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, gs, z, 0, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_zero]
      exact congrArg (fun w => (gs w).toElementMap z) (Fin.ext (by simp))
  | n + 1, gs, z, i + 1, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ,
        component_tupleMap n (fun j => gs j.succ) z i (Nat.lt_of_succ_lt_succ hi)]
      rfl

theorem tupleMap_zero (gs : Fin 0 → ApproximableMap 𝒩 N) :
    tupleMap 0 gs = constMap 𝒩 𝒩.bot := rfl

theorem component_tupleMap_ge : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ), n ≤ i → component ((tupleMap n gs).toElementMap z) i = N.bot
  | 0, gs, z, i, _ => by rw [tupleMap_zero, toElementMap_constMap, component_bot]
  | n + 1, gs, z, i, hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ]
      exact component_tupleMap_ge n (fun k => gs k.succ) z j (by omega)

theorem tupleMap_argLike {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i)) (v : List.Vector ℕ m) :
    ArgLike ((tupleMap nn φg).toElementMap (vecElem v)) := by
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi]; exact realizer_value (hg ⟨i, hi⟩) v
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi)]; exact Or.inl rfl

theorem tupleMap_vecElem_eq {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i))
    (v : List.Vector ℕ m) (w : List.Vector ℕ nn) (hw : ∀ i, w.get i ∈ g i v) :
    (tupleMap nn φg).toElementMap (vecElem v) = vecElem w := by
  apply eq_of_component_eq
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi, component_vecElem_lt w hi]
    exact (hg ⟨i, hi⟩).defined v (w.get ⟨i, hi⟩) (hw ⟨i, hi⟩)
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi), component_vecElem,
      dite_eq_right hi]

theorem vecElem_totals {n : ℕ} (v : List.Vector ℕ n) :
    ∀ j, j < n → ∃ k, component (vecElem v) j = natElem k :=
  fun j hj => ⟨v.get ⟨j, hj⟩, component_vecElem_lt v hj⟩

end DomainTheory.NeighbourhoodSystems.PartrecLam
