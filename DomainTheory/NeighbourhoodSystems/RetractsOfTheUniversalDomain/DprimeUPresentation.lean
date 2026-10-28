module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

def posnegList (δ : ℕ → Bool) : ℕ → List ℕ × List ℕ
  | 0 => ([], [])
  | n + 1 =>
      let pn := posnegList δ n
      if δ n then (pn.1 ++ [n], pn.2) else (pn.1, pn.2 ++ [n])

noncomputable abbrev e : ℕ → Set α := (P0 P).X

@[simp] theorem posnegList_zero (δ : ℕ → Bool) : posnegList δ 0 = ([], []) := rfl

theorem posnegList_succ_true {δ : ℕ → Bool} {n : ℕ} (h : δ n = true) :
    posnegList δ (n + 1) = ((posnegList δ n).1 ++ [n], (posnegList δ n).2) := by
  show (if δ n then _ else _) = _
  simp [h]

theorem posnegList_succ_false {δ : ℕ → Bool} {n : ℕ} (h : δ n = false) :
    posnegList δ (n + 1) = ((posnegList δ n).1, (posnegList δ n).2 ++ [n]) := by
  show (if δ n then _ else _) = _
  simp [h]

theorem IPos_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E) (l1 l2 : List ℕ) :
    IPos Q (l1 ++ l2) = IPos Q l1 ∩ IPos Q l2 := by
  induction l1 with
  | nil => simp [IPos_nil]
  | cons a l ih => rw [List.cons_append, IPos_cons, IPos_cons, ih, Set.inter_assoc]

theorem negPart_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E)
    (n1 n2 : List ℕ) :
    {m : ℕ | ∀ j ∈ (n1 ++ n2), m ∉ idxSet Q.X j} =
      {m | ∀ j ∈ n1, m ∉ idxSet Q.X j} ∩ {m | ∀ j ∈ n2, m ∉ idxSet Q.X j} := by
  ext m
  simp only [Set.mem_ofPred_eq, List.forall_mem_append, Set.mem_inter_iff]

theorem genAtom_eq_DAtom (δ : ℕ → Bool) :
    ∀ n, genAtom (idxSet (e P)) Set.univ δ n =
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 := by
  intro n
  induction n with
  | zero => simp [genAtom, DAtom, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (δ n) with h | h
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_true h, ih]
      unfold DAtom
      rw [IPos_append]
      have hI : IPos (P0 P) [n] = idxSet (e P) n := by
        rw [IPos_cons, IPos_nil, Set.inter_univ]
      rw [hI]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ idxSet (e P) n = _
      ac_rfl
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_false h, ih]
      unfold DAtom
      rw [negPart_append]
      have hZ : {m : ℕ | m ∉ idxSet (e P) n} = Set.univ \ idxSet (e P) n := by
        ext m; simp [Set.mem_sdiff]
      have hn : {m : ℕ | ∀ j ∈ [n], m ∉ idxSet (e P) j} = {m : ℕ | m ∉ idxSet (e P) n} := by
        ext m; simp
      rw [hn, hZ]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ (Set.univ \ idxSet (e P) n) = _
      ac_rfl

theorem eIdx_zero : eIdx P 0 = P.masterIdx := ite_eq_left rfl

theorem genAtom_empty_iff (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 = ∅ := by
  rw [genAtom_eq_DAtom]

theorem hcover : ∀ S, D.mem S ↔ ∃ n, S = e P n := by
  intro S
  constructor
  · intro hS
    obtain ⟨n, hn⟩ := P.surj hS
    exact ⟨eIdx P n, by show S = P.X (eIdx P (eIdx P n)); rw [eIdx_involutive P n]; exact hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact (P0 P).mem_X n

theorem he0 : e P 0 = D.master := by
  show P.X (eIdx P 0) = D.master
  rw [eIdx_zero]; exact P.masterIdx_spec

theorem DprimeU_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff (e P) k t.unpair.1, ← embed_subset_iff (e P) k t.unpair.2])

theorem DprimeU_inter_spec {n m : ℕ}
    (h : ∃ k, Yidx (e P) k ⊆ Yidx (e P) n ∩ Yidx (e P) m) :
    Yidx (e P) ((P0 P).inter n m) = Yidx (e P) n ∩ Yidx (e P) m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff (e P) k n).mpr hk.1)
      ((embed_subset_iff (e P) k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec n m ((P0 P).inter n m)
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp hidx).symm

def capNegCode (t : ℕ) : ℕ := encodeList [t.unpair.2.unpair.2]

theorem capNegCode_eq (a : ℕ) : encodeList [a] = Nat.pair a 0 + 1 := rfl

def capPosCode (t : ℕ) : ℕ := encodeList [t.unpair.1, t.unpair.2.unpair.1]

theorem capPosCode_eq (a b : ℕ) : encodeList [a, b] = Nat.pair a (Nat.pair b 0 + 1) + 1 :=
  rfl

theorem idxSet_inter_eq_iff_DAtom {β : Type*} {V : NeighborhoodSystem β}
    (Q : ComputablePresentation V) (i j k : ℕ) :
    idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k ↔
      Q.X k ⊆ Q.X i ∧ Q.X k ⊆ Q.X j ∧ DAtom Q [i, j] [k] = ∅ := by
  have hDAtom_iff : DAtom Q [i, j] [k] = ∅ ↔ idxSet Q.X i ∩ idxSet Q.X j ⊆ idxSet Q.X k := by
    have hIPos : IPos Q [i, j] = idxSet Q.X i ∩ idxSet Q.X j := by
      rw [IPos_cons, IPos_cons, IPos_nil, Set.inter_univ]
    have hDAtom_eq : DAtom Q [i, j] [k] = (idxSet Q.X i ∩ idxSet Q.X j) \ idxSet Q.X k := by
      show IPos Q [i, j] ∩ {m | ∀ j' ∈ ([k] : List ℕ), m ∉ idxSet Q.X j'} = _
      rw [hIPos]
      ext m
      simp [Set.mem_sdiff]
    rw [hDAtom_eq, Set.sdiff_eq_empty]
  constructor
  · intro heq
    have h1 : idxSet Q.X k ⊆ idxSet Q.X i := by rw [← heq]; exact Set.inter_subset_left
    have h2 : idxSet Q.X k ⊆ idxSet Q.X j := by rw [← heq]; exact Set.inter_subset_right
    exact ⟨(idxSet_subset_iff Q.X k i).mp h1, (idxSet_subset_iff Q.X k j).mp h2,
      hDAtom_iff.mpr heq.subset⟩
  · rintro ⟨hki, hkj, hempty⟩
    exact Set.Subset.antisymm (hDAtom_iff.mp hempty)
      (Set.subset_inter ((idxSet_subset_iff Q.X k i).mpr hki) ((idxSet_subset_iff Q.X k j).mpr hkj))

theorem inclK_i_recDecidable :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem inclK_j_recDecidable :
    RecDecidable₃ (fun _ j k => (P0 P).X k ⊆ (P0 P).X j) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.left.comp Nat.Primrec.right)
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_capNegCode : Nat.Primrec capNegCode := by
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.2) 0) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  refine (primrec_add₂ hinner (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capNegCode t
  rw [capNegCode, capNegCode_eq]

theorem primrec_capPosCode : Nat.Primrec capPosCode := by
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.1) 0 + 1) :=
    primrec_add₂ (Nat.Primrec.pair h2 (Nat.Primrec.const 0)) (Nat.Primrec.const 1)
  have houter : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.1 0 + 1)) :=
    Nat.Primrec.pair Nat.Primrec.left hinner
  refine (primrec_add₂ houter (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capPosCode t
  rw [capPosCode, capPosCode_eq]

theorem DAtom_pair_recDecidable :
    RecDecidable₃ (fun i j k => DAtom (P0 P) [i, j] [k] = ∅) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (capPosCode t) (capNegCode t)) :=
    primrec_capPosCode.pair primrec_capNegCode
  have hp := (DAtom_recDecidable (P0 P)).comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd, capPosCode, capNegCode, decodeList_encodeList]

theorem DprimeU_interEq_computable :
    RecDecidable₃ (fun i j k => Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable P |>.and (inclK_j_recDecidable P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
      (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _),
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

noncomputable def DprimeUPresentation :
    ComputablePresentation (DprimeU D (e P) (hcover P) (he0 P)) where
  X n := Yidx (e P) n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeU_interEq_computable P
  cons_computable := DprimeU_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeU_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yidx_zero D (e P) (hcover P) (he0 P)

theorem DprimeU_isEffectivelyGiven :
    (DprimeU D (e P) (hcover P) (he0 P)).IsEffectivelyGiven :=
  ⟨DprimeUPresentation P⟩

end

end DomainTheory.NeighbourhoodSystems
