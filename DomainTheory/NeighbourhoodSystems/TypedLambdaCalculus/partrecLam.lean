module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.partrecSchemes
public import Mathlib.Computability.PartrecBasis

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.PartrecLam
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

theorem lamDef_of_inner {n : ℕ} (inner : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ)
    (hdef : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → inner.toElementMap (vecElem v) = natElem c)
    (hundef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → inner.toElementMap (vecElem v) = N.bot) :
    LamDef (strictGuardN n inner) f where
  defined v c hc := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hdef v c hc
  undef v hv := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hundef v hv
  strict z hz i hi hb := strictGuardN_strict n inner z hz hi hb

theorem lamDef_comp {m nn : ℕ} (f : List.Vector ℕ nn →. ℕ) (g : Fin nn → List.Vector ℕ m →. ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf f)
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g i)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      (fun v => (List.Vector.mOfFn fun i => g i v) >>= f) := by
  refine lamDef_of_inner (φf.comp (tupleMap nn φg)) _ ?_ ?_
  · intro v c hc
    have hc' : c ∈ (List.Vector.mOfFn fun i => g i v).bind (fun w => f w) := hc
    rw [Part.mem_bind_iff] at hc'
    obtain ⟨w, hw, hcw⟩ := hc'
    rw [toElementMap_comp, tupleMap_vecElem_eq φg g hg v w ((mem_mOfFn _ w).mp hw)]
    exact hf.defined w c hcw
  · intro v hv
    rw [toElementMap_comp]
    by_cases hall : ∀ i, (g i v).Dom
    · set w : List.Vector ℕ nn := List.Vector.ofFn (fun i => (g i v).get (hall i)) with hw_def
      have hwget : ∀ i, w.get i ∈ g i v := by
        intro i; rw [hw_def, List.Vector.get_ofFn]; exact Part.get_mem (hall i)
      rw [tupleMap_vecElem_eq φg g hg v w hwget]
      refine hf.undef w (fun hfw => hv ?_)
      have hmem : (f w).get hfw ∈ (List.Vector.mOfFn fun i => g i v).bind (fun w => f w) := by
        rw [Part.mem_bind_iff]
        exact ⟨w, (mem_mOfFn _ w).mpr hwget, Part.get_mem hfw⟩
      exact Part.dom_iff_mem.mpr ⟨_, hmem⟩
    · rw [not_forall] at hall
      obtain ⟨j, hj⟩ := hall
      refine hf.strict ((tupleMap nn φg).toElementMap (vecElem v))
        (tupleMap_argLike φg g hg v) j j.isLt ?_
      rw [component_tupleMap nn φg (vecElem v) j j.isLt, Fin.eta]
      exact (hg j).undef v hj

theorem lamDef_prec {n : ℕ} (φf φg : ApproximableMap 𝒩 N)
    (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ))
    (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ)) :
    LamDef (strictGuardN (n + 1) (recMap φf φg))
      (((fun v : List.Vector ℕ (n + 1) =>
        v.head.rec (f₀ v.tail) fun y IH => g₀ (y ::ᵥ IH ::ᵥ v.tail)) :
        List.Vector ℕ (n + 1) → ℕ) : List.Vector ℕ (n + 1) →. ℕ) := by
  refine lamDef_of_inner (recMap φf φg) _ (fun v c hc => ?_)
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)
  rw [PFun.coe_val, Part.mem_some_iff] at hc
  subst hc
  obtain ⟨d, u, rfl⟩ := List.Vector.exists_eq_cons v
  rw [List.Vector.head_cons, List.Vector.tail_cons]
  exact recMap_eval φf φg f₀ g₀ hf hg u d

theorem lamDef_primComp {m nn : ℕ} (f₀ : List.Vector ℕ nn → ℕ)
    (g₀ : Fin nn → List.Vector ℕ m → ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf (f₀ : List.Vector ℕ nn →. ℕ))
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g₀ i : List.Vector ℕ m →. ℕ)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      ((fun a => f₀ (List.Vector.ofFn fun i => g₀ i a) : List.Vector ℕ m → ℕ) :
        List.Vector ℕ m →. ℕ) := by
  refine lamDef_congr (fun v => ?_)
    (lamDef_comp (f₀ : _ →. ℕ) (fun i => (g₀ i : _ →. ℕ)) φf hf φg hg)
  simp only [PFun.coe_val, Vector.mOfFn_part_some]
  change (Part.some (List.Vector.ofFn fun i => g₀ i v)).bind (fun w => Part.some (f₀ w))
      = Part.some (f₀ (List.Vector.ofFn fun i => g₀ i v))
  exact Part.bind_some _ _

theorem lamDef_rfind {n : ℕ} (φf : ApproximableMap 𝒩 N) {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) :
    LamDef (strictGuardN n (findMap φf))
      (fun v : List.Vector ℕ n => Nat.rfind (rfindZeroPred f v)) := by
  refine lamDef_of_inner (findMap φf) _ ?_ ?_
  · intro v c hc
    rw [findMap_vecElem]
    have hc' : c ∈ Nat.rfind (rfindZeroPred f v) := hc
    rw [Nat.mem_rfind] at hc'
    obtain ⟨hcs, hcm⟩ := hc'
    have h0 : f (c ::ᵥ v) = 0 := of_decide_eq_true (Part.mem_some_iff.mp hcs).symm
    have hmin : ∀ i, i < c → f (i ::ᵥ v) ≠ 0 :=
      fun i hi => of_decide_eq_false (Part.mem_some_iff.mp (hcm hi)).symm
    exact searchMap_climb φf hf v c h0 hmin c 0 (by omega)
  · intro v hv
    rw [findMap_vecElem]
    have hdiv : ∀ k, f (k ::ᵥ v) ≠ 0 := by
      intro k h0
      refine hv ?_
      have hdom : (Nat.rfind (rfindZeroPred f v)).Dom := by
        rw [Nat.rfind_dom]
        refine ⟨k, ?_, fun {m} _ => trivial⟩
        change true ∈ Part.some (decide (f (k ::ᵥ v) = 0))
        rw [Part.mem_some_iff]
        exact (decide_eq_true_iff.mpr h0).symm
      exact hdom
    exact searchMap_diverge φf hf v hdiv 0

theorem lamDef_total {n : ℕ} (ψ : ApproximableMap 𝒩 N) (g : List.Vector ℕ n → ℕ)
    (hval : ∀ v, ψ.toElementMap (vecElem v) = natElem (g v)) :
    LamDef (strictGuardN n ψ) (g : List.Vector ℕ n →. ℕ) :=
  lamDef_of_inner ψ _
    (fun v c hc => by rw [PFun.coe_val, Part.mem_some_iff] at hc; rw [hval, ← hc])
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)

theorem lamDef_get {n : ℕ} (i : Fin n) :
    LamDef (strictGuardN n (projN N i))
      ((fun v => v.get i : List.Vector ℕ n → ℕ) : List.Vector ℕ n →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_projN, component_vecElem_lt v i.isLt, Fin.eta])

theorem lamDef_succ : LamDef (strictGuardN 1 (succMap.comp (projN N 0)))
    ((fun v => Nat.succ v.head : List.Vector ℕ 1 → ℕ) : List.Vector ℕ 1 →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_comp, toElementMap_projN, component_vecElem_lt v (by norm_num),
      succMap_natElem]
    congr 1
    simp [List.Vector.get_zero])

theorem lamDef_zero : LamDef (strictGuardN 0 (constMap 𝒩 (natElem 0)))
    ((fun _ => 0 : List.Vector ℕ 0 → ℕ) : List.Vector ℕ 0 →. ℕ) :=
  lamDef_total (constMap 𝒩 (natElem 0)) _ (fun v => by rw [toElementMap_constMap])

theorem primrec_lamDef {n : ℕ} {f : List.Vector ℕ n → ℕ} (h : Nat.Primrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ (f : List.Vector ℕ n →. ℕ) := by
  induction h with
  | zero => exact ⟨_, lamDef_zero⟩
  | succ => exact ⟨_, lamDef_succ⟩
  | get i => exact ⟨_, lamDef_get i⟩
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_primComp _ g φf hφf φg hφg⟩
  | prec _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      obtain ⟨φg, hφg⟩ := ihg
      exact ⟨_, lamDef_prec φf φg _ _ hφf hφg⟩

theorem partrec_lamDef {n : ℕ} {f : List.Vector ℕ n →. ℕ} (h : Nat.Partrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ f := by
  induction h with
  | prim hp => exact primrec_lamDef hp
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_comp _ g φf hφf φg hφg⟩
  | rfind _ ih =>
      obtain ⟨φf, hφf⟩ := ih
      exact ⟨_, lamDef_rfind φf hφf⟩

theorem partrec_one {h : ℕ →. ℕ}
    (H : Nat.Partrec' (fun v : List.Vector ℕ 1 => h v.head)) :
    ∃ τ : ApproximableMap N N,
      (∀ a m, m ∈ h a → τ.toElementMap (natElem a) = natElem m) ∧
      (∀ a, ¬ (h a).Dom → τ.toElementMap (natElem a) = N.bot) ∧
      τ.toElementMap N.bot = N.bot := by
  obtain ⟨φ, hφ⟩ := partrec_lamDef H
  refine ⟨φ.comp oneArg, ?_, ?_, ?_⟩
  · intro a m hm
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.defined (a ::ᵥ List.Vector.nil) m ?_
    rwa [List.Vector.head_cons]
  · intro a hdom
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.undef (a ::ᵥ List.Vector.nil) ?_
    rwa [List.Vector.head_cons]
  · rw [toElementMap_comp, oneArg_bot]
    refine hφ.strict 𝒩.bot (fun j => Or.inl (component_bot j)) 0 (by omega) (component_bot 0)

end DomainTheory.NeighbourhoodSystems.PartrecLam
