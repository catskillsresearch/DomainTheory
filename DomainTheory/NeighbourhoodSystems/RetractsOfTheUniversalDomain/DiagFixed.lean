module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α}

def DiagFixed (P : ComputablePresentation V) (a : ApproximableMap V V) (n : ℕ) : Prop :=
  a.rel (P.X n) (P.X n)

theorem diagFixed_iff_fixedNbhd_mem (P : ComputablePresentation V) (a : ApproximableMap V V)
    (n : ℕ) : DiagFixed P a n ↔ (fixedNbhd a).mem (P.X n) :=
  (and_iff_right (P.mem_X n)).symm

theorem diagFixed_isREPred {P : ComputablePresentation V} {a : ApproximableMap V V}
    (ha : ComputableMap P P a) : REPred (DiagFixed P a) := by
  have ha' : REPred (fun t : ℕ => a.rel (P.X t.unpair.1) (P.X t.unpair.2)) := ha.out
  have hdiag : Nat.Primrec (fun n : ℕ => Nat.pair n n) := primrec_id.pair primrec_id
  refine REPred.of_iff (fun n => ?_) (ha'.comp hdiag)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact Iff.rfl

theorem diagFixed_exists_qChar {P : ComputablePresentation V} {a : ApproximableMap V V}
    (ha : ComputableMap P P a) :
    ∃ qChar : ℕ → ℕ, Nat.Primrec qChar ∧
      ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1 := by
  obtain ⟨q, hq, hqe⟩ := diagFixed_isREPred ha
  obtain ⟨f, hf, hfe⟩ := hq
  exact ⟨f, hf, fun n => (hqe n).trans (exists_congr (fun i => hfe _))⟩

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

def myStep (r e : ℕ) : ℕ :=
  selectFn (isOne (qChar e) * isOne (cons (Nat.pair r e.unpair.2)))
    (P.inter r e.unpair.2) r

def myFold (l : List ℕ) : ℕ := l.foldl (myStep P qChar cons) P.masterIdx

@[simp] theorem myFold_nil : myFold P qChar cons [] = P.masterIdx := rfl

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

def myStepCode (w : ℕ) : ℕ := myStep P qChar cons w.unpair.2.unpair.1 w.unpair.1

def myFoldCode (c : ℕ) : ℕ := foldCode (myStepCode P qChar cons) 0 P.masterIdx c

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

theorem diagFixed_masterIdx (a : ApproximableMap V V) : DiagFixed P a P.masterIdx := by
  show a.rel (P.X P.masterIdx) (P.X P.masterIdx)
  rw [P.masterIdx_spec]
  exact a.master_rel
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

theorem myFoldCode_eq (c : ℕ) : myFoldCode P qChar cons c = myFold P qChar cons (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => myStepCode P qChar cons (Nat.pair x (Nat.pair acc 0)))
      = myStep P qChar cons := by
    funext acc x
    unfold myStepCode
    simp only [unpair_pair_fst, unpair_pair_snd]
  unfold myFoldCode myFold
  rw [foldCode_eq', hfun]
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

theorem myFold_cons (e : ℕ) (rest : List ℕ) :
    myFold P qChar cons (e :: rest) = rest.foldl (myStep P qChar cons) (myStep P qChar cons P.masterIdx e) := by
  unfold myFold; rw [List.foldl_cons]
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

theorem myStep_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {r : ℕ} (hr : DiagFixed P a r) (e : ℕ) :
    DiagFixed P a (myStep P qChar cons r e) := by
  unfold myStep
  have hq_dec : ((qChar e) ≠ 1) ∨ ((qChar e) = 1) := by
    by_cases hq : (qChar e) = 1
    · exact Or.inr hq
    · exact Or.inl hq
  rcases hq_dec with hq | hq
  · rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
    exact hr
  · rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair r e.unpair.2)) ≠ 1) ∨ ((cons (Nat.pair r e.unpair.2)) = 1) := by
      by_cases hc : (cons (Nat.pair r e.unpair.2)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero]
      exact hr
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one]
      have hn : DiagFixed P a e.unpair.2 :=
        (hqChar e.unpair.2).mpr ⟨e.unpair.1, by rw [pair_unpair]; exact hq⟩
      obtain ⟨k, hk⟩ := (hcons r e.unpair.2).mp hc
      have hVinter : V.mem (P.X r ∩ P.X e.unpair.2) := by
        rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
      have hfix : (fixedNbhd a).mem (P.X r ∩ P.X e.unpair.2) :=
        (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a r).mp hr)
          ((diagFixed_iff_fixedNbhd_mem P a e.unpair.2).mp hn) hVinter
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]
      exact hfix

theorem myFold_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {r : ℕ}, DiagFixed P a r → DiagFixed P a (l.foldl (myStep P qChar cons) r) := by
  induction l with
  | nil => intro r hr; simpa using hr
  | cons e rest ih =>
    intro r hr
    rw [List.foldl_cons]
    exact ih (myStep_diagFixed_of_diagFixed hqChar hcons hr e)

theorem myFold_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    DiagFixed P a (myFold P qChar cons l) :=
  myFold_diagFixed_of_diagFixed hqChar hcons l (diagFixed_masterIdx a)

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

theorem diagFixed_myFoldCode {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c : ℕ) :
    DiagFixed P a (myFoldCode P qChar cons c) := by
  rw [myFoldCode_eq]
  exact myFold_diagFixed hqChar hcons (decodeList c)

theorem primrec_myStepCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myStepCode P qChar cons) := by
  have he : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) := Nat.Primrec.right.comp he
  have hargs : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    hr.pair he2
  have hqchar_e : Nat.Primrec (fun w : ℕ => qChar w.unpair.1) := hqCharp.comp he
  have hcons_val : Nat.Primrec
      (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)) :=
    hconsp.comp hargs
  have hcond : Nat.Primrec (fun w : ℕ =>
      isOne (qChar w.unpair.1) * isOne (cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))) :=
    primrec_mul₂ (primrec_isOne.comp hqchar_e) (primrec_isOne.comp hcons_val)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    (P.inter_primrec.comp hargs).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hinter hr).of_eq fun _ => rfl

theorem primrec_myFoldCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myFoldCode P qChar cons) :=
  (primrec_foldCode (primrec_myStepCode P qChar cons hqCharp hconsp)
    (Nat.Primrec.const 0) (Nat.Primrec.const P.masterIdx) primrec_id).of_eq
    fun _ => rfl

end

end DomainTheory.NeighbourhoodSystems
