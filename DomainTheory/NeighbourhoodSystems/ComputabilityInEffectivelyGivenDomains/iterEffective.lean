module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.scottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.smashEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap SmashProduct

variable {α β γ : Type*}

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

def iterIdx (t j : ℕ) : ℕ := nthCode t j P.masterIdx

def iterEnum (t : ℕ) : Set (ℕ × α) := {p | p.2 ∈ P.X (iterIdx P t p.1)}

end Iterate
section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

@[simp] theorem fiber_iterEnum (t j : ℕ) : fiber (iterEnum P t) j = P.X (iterIdx P t j) := rfl

theorem exists_list_fiber {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    ∀ N, ∃ L : List ℕ, L.length = N ∧ ∀ j, j < N → P.X (L.getD j P.masterIdx) = fiber W j := by
  intro N
  induction N with
  | zero => exact ⟨[], rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    obtain ⟨L, hlen, hL⟩ := ih
    obtain ⟨n, hn⟩ := P.surj (hW.1 N)
    refine ⟨L ++ [n], by simp [List.length_append, hlen], fun j hj => ?_⟩
    by_cases h : j < N
    · rw [getD_append_cf L [n] P.masterIdx (by rw [hlen]; exact h)]
      exact hL j h
    · have hjN : j = N := by omega
      subst hjN
      rw [getD_append_right_cf L [n] P.masterIdx hlen.le, hlen, Nat.sub_self,
        List.getD_cons_zero]
      exact hn

def interG (P : ComputablePresentation V) (s : ℕ) : ℕ :=
  P.inter (iterIdx P s.unpair.2.unpair.1 s.unpair.1) (iterIdx P s.unpair.2.unpair.2 s.unpair.1)

theorem iterIdx_ge {t j : ℕ} (h : t ≤ j) : iterIdx P t j = P.masterIdx := by
  unfold iterIdx
  rw [nthCode_eq, getD_eq_default_cf]
  exact le_trans (decodeList_length_le t) h

theorem iterEnum_inter_eq_iff {n m k : ℕ} :
    iterEnum P n ∩ iterEnum P m = iterEnum P k ↔
      ∀ j, j < n + m + k →
        P.X (iterIdx P n j) ∩ P.X (iterIdx P m j) = P.X (iterIdx P k j) := by
  constructor
  · intro h j _
    have := congrArg (fun W => fiber W j) h
    simpa only [fiber_inter, fiber_iterEnum] using this
  · intro h
    apply eq_of_fiber_eq
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m + k
    · exact h j hj
    · rw [iterIdx_ge (show n ≤ j by omega), iterIdx_ge (show m ≤ j by omega),
        iterIdx_ge (show k ≤ j by omega), P.masterIdx_spec, Set.inter_self]

theorem iterEnum_mem (t : ℕ) : (iterSys V).mem (iterEnum P t) := by
  refine ⟨fun j => ?_, t, fun j hj => ?_⟩
  · rw [fiber_iterEnum]; exact P.mem_X _
  · rw [fiber_iterEnum, iterIdx_ge hj, P.masterIdx_spec]

def iterInter (P : ComputablePresentation V) (n m : ℕ) : ℕ :=
  tabCode (interG P) (Nat.pair (n + m) (Nat.pair n m)) (n + m)

theorem iterInter_idx_ge {n m j : ℕ} (hj : n + m ≤ j) :
    iterIdx P (iterInter P n m) j = P.masterIdx := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_ge hj]

theorem iterInter_idx_lt {n m j : ℕ} (hj : j < n + m) :
    iterIdx P (iterInter P n m) j = P.inter (iterIdx P n j) (iterIdx P m j) := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_lt hj]
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem iterEnum_cons_iff {n m : ℕ} :
    (∃ k, iterEnum P k ⊆ iterEnum P n ∩ iterEnum P m) ↔
      ∀ j, j < n + m → ∃ i, P.X i ⊆ P.X (iterIdx P n j) ∩ P.X (iterIdx P m j) := by
  constructor
  · rintro ⟨k, hk⟩ j _
    refine ⟨iterIdx P k j, ?_⟩
    have := fiber_mono hk j
    rwa [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum] at this
  · intro h
    refine ⟨iterInter P n m, ?_⟩
    apply subset_of_fiber_subset
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m
    · rw [iterInter_idx_lt hj]
      obtain ⟨i, hi⟩ := h j hj
      rw [P.inter_spec ⟨i, hi⟩]
    · rw [iterInter_idx_ge (by omega), iterIdx_ge (show n ≤ j by omega),
        iterIdx_ge (show m ≤ j by omega), P.masterIdx_spec, Set.inter_self]

end Iterate
section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem primrec_iterIdx_proj {codeProj : ℕ → ℕ} (hc : Nat.Primrec codeProj) :
    Nat.Primrec (fun w => iterIdx P (codeProj w) w.unpair.1) := by
  refine (primrec_nthCode.comp (hc.pair (Nat.Primrec.left.pair
    (Nat.Primrec.const P.masterIdx)))).of_eq (fun w => ?_)
  simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]

theorem primrec_interG : Nat.Primrec (interG P) := by
  have hA : Nat.Primrec (fun s => iterIdx P s.unpair.2.unpair.1 s.unpair.1) :=
    primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
  have hB : Nat.Primrec (fun s => iterIdx P s.unpair.2.unpair.2 s.unpair.1) :=
    primrec_iterIdx_proj (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (P.inter_primrec.comp (hA.pair hB)).of_eq (fun s => ?_)
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

noncomputable def iterPresentation (P : ComputablePresentation V) :
    ComputablePresentation (iterSys V) where
  X := iterEnum P
  mem_X := iterEnum_mem
  surj := by
    rintro W hW
    obtain ⟨N, hN⟩ := hW.2
    obtain ⟨L, hlen, hL⟩ := exists_list_fiber (P := P) hW N
    refine ⟨encodeList L, ?_⟩
    apply eq_of_fiber_eq
    intro j
    show P.X (nthCode (encodeList L) j P.masterIdx) = fiber W j
    rw [nthCode_eq, decodeList_encodeList]
    by_cases hj : j < N
    · exact hL j hj
    · rw [getD_eq_default_cf L P.masterIdx (by rw [hlen]; omega), P.masterIdx_spec,
        hN j (by omega)]
  interEq_computable := by
    have hbound : Nat.Primrec
        (fun t : ℕ => t.unpair.1 + t.unpair.2.unpair.1 + t.unpair.2.unpair.2) :=
      primrec_add₂ (primrec_add₂ Nat.Primrec.left (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.right.comp Nat.Primrec.right)
    have hA : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
    have hB : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hC : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2.unpair.2 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hq : RecDecidable (fun w => P.X (iterIdx P w.unpair.2.unpair.1 w.unpair.1)
        ∩ P.X (iterIdx P w.unpair.2.unpair.2.unpair.1 w.unpair.1)
        = P.X (iterIdx P w.unpair.2.unpair.2.unpair.2 w.unpair.1)) := by
      refine RecDecidable.of_iff (fun w => ?_) (P.interEq_computable.comp (hA.pair (hB.pair hC)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hq.bForall hbound)
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact iterEnum_inter_eq_iff
  cons_computable := by
    have hbound : Nat.Primrec (fun t : ℕ => t.unpair.1 + t.unpair.2) :=
      primrec_add₂ Nat.Primrec.left Nat.Primrec.right
    have hA : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
    have hB : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.right.comp Nat.Primrec.right)
    have hq : RecDecidable (fun w => ∃ i, P.X i ⊆ P.X (iterIdx P w.unpair.2.unpair.1 w.unpair.1)
        ∩ P.X (iterIdx P w.unpair.2.unpair.2 w.unpair.1)) := by
      refine RecDecidable.of_iff (fun w => ?_) (P.cons_computable.comp (hA.pair hB))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hq.bForall hbound)
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact iterEnum_cons_iff
  inter := iterInter P
  inter_primrec := by
    have hr : Nat.Primrec (fun t => Nat.pair
        (Nat.pair (t.unpair.1 + t.unpair.2) (Nat.pair t.unpair.1 t.unpair.2))
        (t.unpair.1 + t.unpair.2)) :=
      ((primrec_add₂ Nat.Primrec.left Nat.Primrec.right).pair
        (Nat.Primrec.left.pair Nat.Primrec.right)).pair
        (primrec_add₂ Nat.Primrec.left Nat.Primrec.right)
    refine ((primrec_tabCode (primrec_interG (P := P))).comp hr).of_eq (fun t => ?_)
    show tabCode (interG P) _ _ = iterInter P t.unpair.1 t.unpair.2
    unfold iterInter
    simp only [unpair_pair_fst, unpair_pair_snd]
  inter_spec := by
    intro n m hcons
    apply eq_of_fiber_eq
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m
    · rw [iterInter_idx_lt hj, P.inter_spec ((iterEnum_cons_iff (P := P)).mp hcons j hj)]
    · rw [iterInter_idx_ge (by omega), iterIdx_ge (show n ≤ j by omega),
        iterIdx_ge (show m ≤ j by omega), P.masterIdx_spec, Set.inter_self]
  masterIdx := 0
  masterIdx_spec := by
    apply eq_of_fiber_eq
    intro j
    rw [fiber_iterEnum, fiber_iterSys_master, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]

end Iterate
section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

@[simp] theorem iterPresentation_X (t : ℕ) : (iterPresentation P).X t = iterEnum P t := rfl

end Iterate
section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem iterSys_isEffectivelyGiven (e : V.IsEffectivelyGiven) :
    (iterSys V).IsEffectivelyGiven := by
  obtain ⟨Q⟩ := e
  exact ⟨iterPresentation (P := Q)⟩

end Iterate
section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem projN_isComputable (P : ComputablePresentation V) (n : ℕ) :
    ComputableMap (iterPresentation P) P (projN V n) := by
  constructor
  have hincl : RecDecidable (fun s => P.X s.unpair.1 ⊆ P.X s.unpair.2) := P.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (nthCode t.unpair.1 n P.masterIdx) t.unpair.2) :=
    ((primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.const n).pair (Nat.Primrec.const P.masterIdx)))).of_eq
        (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [iterPresentation_X, projN_rel, fiber_iterEnum, iterIdx, unpair_pair_fst,
    unpair_pair_snd]
  exact ⟨fun h => h.2.2, fun h => ⟨iterEnum_mem _, P.mem_X _, h⟩⟩

end Iterate

end DomainTheory.NeighbourhoodSystems
