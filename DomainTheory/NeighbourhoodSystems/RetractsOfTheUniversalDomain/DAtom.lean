module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

def IPos (pos : List ℕ) : Set ℕ := {m | ∀ i ∈ pos, m ∈ idxSet P.X i}

@[simp] theorem IPos_nil : IPos P [] = Set.univ := by
  ext m; simp [IPos]

def DAtom (pos neg : List ℕ) : Set ℕ := IPos P pos ∩ {m | ∀ j ∈ neg, m ∉ idxSet P.X j}

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

def meetStep (r i : ℕ) : ℕ :=
  selectFn (isOne r.unpair.1 * isOne (cons (Nat.pair r.unpair.2 i)))
    (Nat.pair 1 (P.inter r.unpair.2 i)) (Nat.pair 0 r.unpair.2)

def meetFold (l : List ℕ) : ℕ := l.foldl (meetStep P cons) (Nat.pair 1 P.masterIdx)

@[simp] theorem meetFold_nil : meetFold P cons [] = Nat.pair 1 P.masterIdx := rfl

def meetStepCode (w : ℕ) : ℕ := meetStep P cons w.unpair.2.unpair.1 w.unpair.1

def meetFoldCode (c : ℕ) : ℕ := foldCode (meetStepCode P cons) 0 (Nat.pair 1 P.masterIdx) c

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)
variable (incl : ℕ → ℕ)

def DAtomEmptyChar (posC negC : ℕ) : ℕ :=
  selectFn (isOne (meetFoldCode P cons posC).unpair.1)
    (existsListChar (fun t => incl (Nat.pair t.unpair.2 t.unpair.1))
      (meetFoldCode P cons posC).unpair.2 negC)
    1
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem IPos_cons (i : ℕ) (rest : List ℕ) :
    IPos P (i :: rest) = idxSet P.X i ∩ IPos P rest := by
  ext m
  simp only [IPos, Set.mem_ofPred_eq, List.mem_cons, mem_idxSet, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨h i (Or.inl rfl), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨hi, hrest⟩ j (rfl | hj)
    · exact hi
    · exact hrest j hj

theorem idxSet_masterIdx_eq_univ : idxSet P.X P.masterIdx = Set.univ :=
  Set.eq_univ_of_forall fun m => by
    show P.X m ⊆ P.X P.masterIdx
    rw [P.masterIdx_spec]
    exact D.sub_master (P.mem_X m)

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

theorem meetFoldCode_eq (c : ℕ) : meetFoldCode P cons c = meetFold P cons (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => meetStepCode P cons (Nat.pair x (Nat.pair acc 0)))
      = meetStep P cons := by
    funext acc x
    unfold meetStepCode
    simp only [unpair_pair_fst, unpair_pair_snd]
  unfold meetFoldCode meetFold
  rw [foldCode_eq', hfun]

theorem meetFold_cons (i : ℕ) (rest : List ℕ) :
    meetFold P cons (i :: rest) = (rest.foldl (meetStep P cons) (meetStep P cons
      (Nat.pair 1 P.masterIdx) i)) := by
  unfold meetFold; rw [List.foldl_cons]

theorem meetStep_ok_le_one (r i : ℕ) : (meetStep P cons r i).unpair.1 ≤ 1 := by
  have h1 := isOne_le_one r.unpair.1
  have h2 := isOne_le_one (cons (Nat.pair r.unpair.2 i))
  unfold meetStep
  rcases (show isOne r.unpair.1 = 0 ∨ isOne r.unpair.1 = 1 by omega) with h | h
  · rw [h, Nat.zero_mul, selectFn_zero, unpair_pair_fst]; exact Nat.zero_le 1
  · rw [h, Nat.one_mul]
    rcases (show isOne (cons (Nat.pair r.unpair.2 i)) = 0 ∨
        isOne (cons (Nat.pair r.unpair.2 i)) = 1 by omega) with h' | h'
    · rw [h', selectFn_zero, unpair_pair_fst]; exact Nat.zero_le 1
    · rw [h', selectFn_one, unpair_pair_fst]

theorem meetStep_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {init : ℕ} {S : Set ℕ} (hle : init.unpair.1 ≤ 1)
    (h1 : init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S)
    (h0 : init.unpair.1 = 0 → S = ∅) (i : ℕ) :
    (meetStep P cons init i).unpair.1 ≤ 1 ∧
      ((meetStep P cons init i).unpair.1 = 1 →
        idxSet P.X (meetStep P cons init i).unpair.2 = S ∩ idxSet P.X i) ∧
      ((meetStep P cons init i).unpair.1 = 0 → S ∩ idxSet P.X i = ∅) := by
  refine ⟨meetStep_ok_le_one P cons init i, ?_, ?_⟩ <;>
    (unfold meetStep
     rcases (show init.unpair.1 = 0 ∨ init.unpair.1 = 1 by omega) with hi | hi)
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro h; exact absurd h (by decide)
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro h; exact absurd h (by decide)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_snd, unpair_pair_fst]
      intro _
      have heq : P.X init.unpair.2 ∩ P.X i = P.X (P.inter init.unpair.2 i) :=
        (P.inter_spec (hcons _ _ |>.mp hc)).symm
      rw [← idxSet_inter_of_inter_eq (e := P.X) heq, h1 hi]
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro _
    rw [h0 hi]; simp
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro _
      rw [← h1 hi]
      ext m
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hm1 hm2
      exact hc ((hcons _ _).mpr ⟨m, Set.subset_inter hm1 hm2⟩)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_fst]
      intro h; exact absurd h (by decide)

theorem meetFold_foldl_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {init : ℕ} {S : Set ℕ}, init.unpair.1 ≤ 1 →
      (init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S) → (init.unpair.1 = 0 → S = ∅) →
      (l.foldl (meetStep P cons) init).unpair.1 ≤ 1 ∧
        ((l.foldl (meetStep P cons) init).unpair.1 = 1 →
          idxSet P.X (l.foldl (meetStep P cons) init).unpair.2 = S ∩ IPos P l) ∧
        ((l.foldl (meetStep P cons) init).unpair.1 = 0 → S ∩ IPos P l = ∅) := by
  induction l with
  | nil =>
    intro init S hle h1 h0
    simpa using ⟨hle, h1, h0⟩
  | cons i rest ih =>
    intro init S hle h1 h0
    rw [List.foldl_cons, IPos_cons, ← Set.inter_assoc]
    obtain ⟨hle', h1', h0'⟩ := meetStep_spec P cons hcons hle h1 h0 i
    exact ih hle' h1' h0'

theorem meetFold_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (pos : List ℕ) :
    (meetFold P cons pos).unpair.1 ≤ 1 ∧
      ((meetFold P cons pos).unpair.1 = 1 →
        idxSet P.X (meetFold P cons pos).unpair.2 = IPos P pos) ∧
      ((meetFold P cons pos).unpair.1 = 0 → IPos P pos = ∅) := by
  have hinit1 : (Nat.pair 1 P.masterIdx).unpair.1 = 1 := unpair_pair_fst 1 P.masterIdx
  have hinit2 : (Nat.pair 1 P.masterIdx).unpair.2 = P.masterIdx := unpair_pair_snd 1 P.masterIdx
  have h := meetFold_foldl_spec P cons hcons pos (init := Nat.pair 1 P.masterIdx) (S := Set.univ)
    (by rw [hinit1]) (fun _ => by rw [hinit2]; exact idxSet_masterIdx_eq_univ P)
    (fun h => absurd (hinit1.symm.trans h) (by norm_num))
  simpa only [meetFold, Set.univ_inter] using h

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem mem_IPos {pos : List ℕ} {m : ℕ} : m ∈ IPos P pos ↔ ∀ i ∈ pos, P.X m ⊆ P.X i := Iff.rfl

theorem mem_DAtom {pos neg : List ℕ} {m : ℕ} :
    m ∈ DAtom P pos neg ↔ (∀ i ∈ pos, P.X m ⊆ P.X i) ∧ (∀ j ∈ neg, ¬ P.X m ⊆ P.X j) := by
  simp only [DAtom, Set.mem_inter_iff, mem_IPos, Set.mem_ofPred_eq, mem_idxSet]

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

theorem DAtom_eq_empty_iff
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (pos neg : List ℕ) :
    DAtom P pos neg = ∅ ↔
      (meetFold P cons pos).unpair.1 ≠ 1 ∨
        ∃ j ∈ neg, P.X (meetFold P cons pos).unpair.2 ⊆ P.X j := by
  obtain ⟨hle, h1, h0⟩ := meetFold_spec P cons hcons pos
  set r := meetFold P cons pos with hrdef
  rcases (show r.unpair.1 = 0 ∨ r.unpair.1 = 1 by omega) with hr | hr
  · have hIPos : IPos P pos = ∅ := h0 hr
    simp only [hr, ne_eq, zero_ne_one, not_false_eq_true, true_or, iff_true]
    ext m
    simp only [DAtom, hIPos, Set.mem_inter_iff, Set.mem_empty_iff_false, false_and,
      Set.mem_empty_iff_false]
  · have hIPos : idxSet P.X r.unpair.2 = IPos P pos := h1 hr
    simp only [hr, ne_eq, not_true_eq_false, false_or]
    constructor
    · intro hempty
      by_contra hcon
      push Not at hcon
      have hmem : r.unpair.2 ∈ DAtom P pos neg := by
        rw [mem_DAtom]
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have hself : r.unpair.2 ∈ IPos P pos := hIPos ▸ self_mem_idxSet P.X r.unpair.2
          exact hself i hi
        · exact hcon j hj
      rw [hempty] at hmem
      exact absurd hmem (Set.notMem_empty _)
    · rintro ⟨j, hj, hsub⟩
      ext m
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hmem
      rw [mem_DAtom] at hmem
      have hmsub : P.X m ⊆ P.X r.unpair.2 := by
        have hmI : m ∈ IPos P pos := hmem.1
        rw [← hIPos] at hmI
        exact hmI
      exact hmem.2 j hj (hmsub.trans hsub)
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)
variable (incl : ℕ → ℕ)

theorem DAtomEmptyChar_eq_one_iff
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    (hincl : ∀ n m, incl (Nat.pair n m) = 1 ↔ P.X n ⊆ P.X m) (posC negC : ℕ) :
    DAtomEmptyChar P cons incl posC negC = 1 ↔
      DAtom P (decodeList posC) (decodeList negC) = ∅ := by
  rw [DAtom_eq_empty_iff P cons hcons, ← meetFoldCode_eq]
  set r := meetFoldCode P cons posC with hrdef
  unfold DAtomEmptyChar
  by_cases hok : r.unpair.1 = 1
  · rw [(isOne_eq_one_iff _).mpr hok, selectFn_one, existsListChar_eq_one_iff]
    simp only [ne_eq, hok, not_true_eq_false, false_or]
    constructor
    · rintro ⟨j, hj, hgj⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hgj
      exact ⟨j, hj, (hincl _ _).mp hgj⟩
    · rintro ⟨j, hj, hsub⟩
      refine ⟨j, hj, ?_⟩
      simp only [unpair_pair_fst, unpair_pair_snd]
      exact (hincl _ _).mpr hsub
  · rw [isOne_of_ne_one hok, selectFn_zero]
    simp only [ne_eq, hok, not_false_eq_true, true_or]
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

theorem primrec_meetStepCode (hconsp : Nat.Primrec cons) : Nat.Primrec (meetStepCode P cons) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hrok : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) := Nat.Primrec.left.comp hr
  have hridx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp hr
  have hconstest : Nat.Primrec (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1.unpair.2 w.unpair.1)) :=
    hconsp.comp (hridx.pair hx)
  have hcond : Nat.Primrec
      (fun w : ℕ => isOne w.unpair.2.unpair.1.unpair.1 * isOne
        (cons (Nat.pair w.unpair.2.unpair.1.unpair.2 w.unpair.1))) :=
    primrec_mul₂ (primrec_isOne.comp hrok) (primrec_isOne.comp hconstest)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1.unpair.2 w.unpair.1) :=
    (P.inter_primrec.comp (hridx.pair hx)).of_eq
      (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hthen : Nat.Primrec
      (fun w : ℕ => Nat.pair 1 (P.inter w.unpair.2.unpair.1.unpair.2 w.unpair.1)) :=
    (Nat.Primrec.const 1).pair hinter
  have helse : Nat.Primrec (fun w : ℕ => Nat.pair 0 w.unpair.2.unpair.1.unpair.2) :=
    (Nat.Primrec.const 0).pair hridx
  exact (primrec_selectFn hcond hthen helse).of_eq (fun _ => rfl)

theorem primrec_meetFoldCode (hconsp : Nat.Primrec cons) :
    Nat.Primrec (meetFoldCode P cons) :=
  (primrec_foldCode (primrec_meetStepCode P cons hconsp) (Nat.Primrec.const 0)
    (Nat.Primrec.const (Nat.pair 1 P.masterIdx)) primrec_id).of_eq (fun _ => rfl)

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)
variable (incl : ℕ → ℕ)

theorem primrec_DAtomEmptyChar (hconsp : Nat.Primrec cons) (hinclp : Nat.Primrec incl) :
    Nat.Primrec (fun t => DAtomEmptyChar P cons incl t.unpair.1 t.unpair.2) := by
  have hmf : Nat.Primrec (fun t : ℕ => meetFoldCode P cons t.unpair.1) :=
    (primrec_meetFoldCode P cons hconsp).comp Nat.Primrec.left
  have hmfok : Nat.Primrec (fun t : ℕ => (meetFoldCode P cons t.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hmf
  have hmfidx : Nat.Primrec (fun t : ℕ => (meetFoldCode P cons t.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hmf
  have hg : Nat.Primrec (fun s : ℕ => incl (Nat.pair s.unpair.2 s.unpair.1)) :=
    hinclp.comp (Nat.Primrec.right.pair Nat.Primrec.left)
  have hexists : Nat.Primrec
      (fun t : ℕ => existsListChar (fun s => incl (Nat.pair s.unpair.2 s.unpair.1))
        (meetFoldCode P cons t.unpair.1).unpair.2 t.unpair.2) := by
    have hcomb : Nat.Primrec (fun t : ℕ =>
        Nat.pair t.unpair.2 (meetFoldCode P cons t.unpair.1).unpair.2) :=
      Nat.Primrec.right.pair hmfidx
    exact ((primrec_existsListChar hg).comp hcomb).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  exact (primrec_selectFn (primrec_isOne.comp hmfok) hexists (Nat.Primrec.const 1)).of_eq
    (fun _ => rfl)

theorem DAtom_recDecidable :
    RecDecidable₂ (fun posC negC => DAtom P (decodeList posC) (decodeList negC) = ∅) := by
  obtain ⟨cons, hconsp, hconss⟩ := P.cons_computable
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have := hconss (Nat.pair n m)
    simpa only [unpair_pair_fst, unpair_pair_snd] using this.symm
  have hincl : ∀ n m, incl (Nat.pair n m) = 1 ↔ P.X n ⊆ P.X m := by
    intro n m
    have := hincls (Nat.pair n m)
    simpa only [unpair_pair_fst, unpair_pair_snd] using this.symm
  refine ⟨fun t => DAtomEmptyChar P cons incl t.unpair.1 t.unpair.2,
    primrec_DAtomEmptyChar P cons incl hconsp hinclp, fun t => ?_⟩
  exact (DAtomEmptyChar_eq_one_iff P cons incl hcons hincl t.unpair.1 t.unpair.2).symm

end

end DomainTheory.NeighbourhoodSystems
