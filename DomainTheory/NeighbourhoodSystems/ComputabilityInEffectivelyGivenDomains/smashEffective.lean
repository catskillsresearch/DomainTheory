module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.scottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap

section
variable {α β γ : Type*}
open SmashProduct

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

open scoped Classical in

noncomputable def smashEnum (t : ℕ) : Set (α ⊕ β) :=
  if P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master then
    prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2)
  else prodNbhd V₀.master V₁.master

end Smash

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

open scoped Classical in
theorem smashEnum_master {t : ℕ}
    (h : ¬(P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master)) :
    smashEnum P₀ P₁ t = prodNbhd V₀.master V₁.master := ite_eq_right h

open scoped Classical in
theorem smashEnum_proper {t : ℕ}
    (h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master) :
    smashEnum P₀ P₁ t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := ite_eq_left h

theorem smashEnum_eq_eff {c₀ c₁ : ℕ → ℕ} (hc₀le : ∀ n, c₀ n ≤ 1) (hc₁le : ∀ n, c₁ n ≤ 1)
    (hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1) (hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1) (t : ℕ) :
    smashEnum P₀ P₁ t =
      prodNbhd (P₀.X (selectFn (c₀ t.unpair.1 * c₁ t.unpair.2) t.unpair.1 P₀.masterIdx))
        (P₁.X (selectFn (c₀ t.unpair.1 * c₁ t.unpair.2) t.unpair.2 P₁.masterIdx)) := by
  by_cases h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master
  · have e0 : c₀ t.unpair.1 = 1 := (hc₀ _).mp h.1
    have e1 : c₁ t.unpair.2 = 1 := (hc₁ _).mp h.2
    rw [smashEnum_proper h, e0, e1, mul_one, selectFn_one, selectFn_one]
  · rw [smashEnum_master h]
    have hpf : c₀ t.unpair.1 * c₁ t.unpair.2 = 0 := by
      rcases not_and_or.mp h with h0 | h1
      · have hz : c₀ t.unpair.1 = 0 := by
          have hle := hc₀le t.unpair.1
          rcases (show c₀ t.unpair.1 = 0 ∨ c₀ t.unpair.1 = 1 by omega) with h | h
          · exact h
          · exact absurd ((hc₀ _).mpr h) h0
        rw [hz, Nat.zero_mul]
      · have hz : c₁ t.unpair.2 = 0 := by
          have hle := hc₁le t.unpair.2
          rcases (show c₁ t.unpair.2 = 0 ∨ c₁ t.unpair.2 = 1 by omega) with h | h
          · exact h
          · exact absurd ((hc₁ _).mpr h) h1
        rw [hz, Nat.mul_zero]
    rw [hpf, selectFn_zero, selectFn_zero, P₀.masterIdx_spec, P₁.masterIdx_spec]

theorem smashEnum_eq_prodNbhd_mem (k : ℕ) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ smashEnum P₀ P₁ k = prodNbhd A B := by
  by_cases h : P₀.X k.unpair.1 ≠ V₀.master ∧ P₁.X k.unpair.2 ≠ V₁.master
  · exact ⟨_, _, P₀.mem_X _, P₁.mem_X _, smashEnum_proper h⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, smashEnum_master h⟩

theorem smashEnum_mem (t : ℕ) : (smash V₀ V₁).mem (smashEnum P₀ P₁ t) := by
  by_cases h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master
  · rw [smashEnum_proper h]; exact smash_mem_proper (P₀.mem_X _) h.1 (P₁.mem_X _) h.2
  · rw [smashEnum_master h]; exact (smash V₀ V₁).master_mem

theorem smashEnum_subset_master (k : ℕ) :
    smashEnum P₀ P₁ k ⊆ prodNbhd V₀.master V₁.master := by
  have h := (smash V₀ V₁).sub_master (smashEnum_mem (P₀ := P₀) (P₁ := P₁) k)
  rwa [smash_master] at h

end Smash

end

section
variable {α β γ : Type*}
open SmashProduct

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

theorem proper₀_dec : RecDecidable (fun n => P₀.X n ≠ V₀.master) := by
  have heq : RecDecidable (fun n => P₀.X n = V₀.master) := by
    refine RecDecidable.of_iff (fun n => ?_)
      (P₀.eq_computable.comp (primrec_id.pair (Nat.Primrec.const P₀.masterIdx)))
    simp only [unpair_pair_fst, unpair_pair_snd, P₀.masterIdx_spec, id_eq]
  exact heq.not

theorem proper₁_dec : RecDecidable (fun n => P₁.X n ≠ V₁.master) := by
  have heq : RecDecidable (fun n => P₁.X n = V₁.master) := by
    refine RecDecidable.of_iff (fun n => ?_)
      (P₁.eq_computable.comp (primrec_id.pair (Nat.Primrec.const P₁.masterIdx)))
    simp only [unpair_pair_fst, unpair_pair_snd, P₁.masterIdx_spec, id_eq]
  exact heq.not

end Smash

end

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap SmashProduct

variable {α β γ : Type*}

section Smash
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
variable {P₀ P₁}
variable (P₀ P₁)

noncomputable def smashPresentation : ScottPresentation (smash V₀ V₁) where
  X := smashEnum P₀ P₁
  mem_X := smashEnum_mem
  surj := by
    rintro Z (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩)
    · refine ⟨Nat.pair P₀.masterIdx P₁.masterIdx, ?_⟩
      rw [smashEnum_master (by
        rw [unpair_pair_fst, P₀.masterIdx_spec]; exact fun h => h.1 rfl)]
    · obtain ⟨n, rfl⟩ := P₀.surj hX
      obtain ⟨m, rfl⟩ := P₁.surj hY
      refine ⟨Nat.pair n m, ?_⟩
      rw [smashEnum_proper (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨hXne, hYne⟩),
        unpair_pair_fst, unpair_pair_snd]
  interEq_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
    set c₀ := fun n => isOne (f₀ n) with hc₀def
    set c₁ := fun n => isOne (f₁ n) with hc₁def
    have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
    have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
    have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
      rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
    have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
      rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
    have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
    have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
    have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
      (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
        (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])

    have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
        n.unpair.1 P₀.masterIdx) :=
      primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
    have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
        n.unpair.2 P₁.masterIdx) :=
      primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)

    have hgL : Nat.Primrec (fun t => Nat.pair
        (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.1 P₀.masterIdx)
        (Nat.pair
          (selectFn (c₀ t.unpair.2.unpair.1.unpair.1 * c₁ t.unpair.2.unpair.1.unpair.2)
            t.unpair.2.unpair.1.unpair.1 P₀.masterIdx)
          (selectFn (c₀ t.unpair.2.unpair.2.unpair.1 * c₁ t.unpair.2.unpair.2.unpair.2)
            t.unpair.2.unpair.2.unpair.1 P₀.masterIdx))) :=
      (heffLp.comp Nat.Primrec.left).pair
        ((heffLp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (heffLp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    have hgR : Nat.Primrec (fun t => Nat.pair
        (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.2 P₁.masterIdx)
        (Nat.pair
          (selectFn (c₀ t.unpair.2.unpair.1.unpair.1 * c₁ t.unpair.2.unpair.1.unpair.2)
            t.unpair.2.unpair.1.unpair.2 P₁.masterIdx)
          (selectFn (c₀ t.unpair.2.unpair.2.unpair.1 * c₁ t.unpair.2.unpair.2.unpair.2)
            t.unpair.2.unpair.2.unpair.2 P₁.masterIdx))) :=
      (heffRp.comp Nat.Primrec.left).pair
        ((heffRp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (heffRp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_)
      ((P₀.interEq_computable.comp hgL).and (P₁.interEq_computable.comp hgR))
    dsimp only
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁,
      smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd.inter, prodNbhd_eq_iff]
  cons_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁

    have hpa : RecDecidable (fun t => ¬(P₀.X t.unpair.1.unpair.1 ≠ V₀.master
        ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master)) := by
      have h0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.1 ≠ V₀.master) :=
        (proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.left)
      have h1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
        (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
      exact (h0.and h1).not
    have hpb : RecDecidable (fun t => ¬(P₀.X t.unpair.2.unpair.1 ≠ V₀.master
        ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master)) := by
      have h0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.1 ≠ V₀.master) :=
        (proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.right)
      have h1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
        (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
      exact (h0.and h1).not
    have hcons0 : RecDecidable (fun t => ∃ k, P₀.X k ⊆ P₀.X t.unpair.1.unpair.1
        ∩ P₀.X t.unpair.2.unpair.1) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₀.cons_computable.comp
        ((Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.left.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hcons1 : RecDecidable (fun t => ∃ k, P₁.X k ⊆ P₁.X t.unpair.1.unpair.2
        ∩ P₁.X t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₁.cons_computable.comp
        ((Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hpa.or (hpb.or (hcons0.and hcons1)))
    constructor
    · rintro ⟨k, hk⟩
      by_cases hpa' : P₀.X t.unpair.1.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
      · by_cases hpb' : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · rw [smashEnum_proper hpa', smashEnum_proper hpb', prodNbhd.inter] at hk
            obtain ⟨A, B, hA, _, hkeq⟩ := smashEnum_eq_prodNbhd_mem (P₀ := P₀) (P₁ := P₁) k
            rw [hkeq] at hk
            obtain ⟨hAsub, _⟩ := prodNbhd.subset_iff.mp hk
            obtain ⟨j₀, hj₀⟩ := P₀.surj hA
            exact ⟨j₀, by rw [hj₀]; exact hAsub⟩
          · rw [smashEnum_proper hpa', smashEnum_proper hpb', prodNbhd.inter] at hk
            obtain ⟨A, B, _, hB, hkeq⟩ := smashEnum_eq_prodNbhd_mem (P₀ := P₀) (P₁ := P₁) k
            rw [hkeq] at hk
            obtain ⟨_, hBsub⟩ := prodNbhd.subset_iff.mp hk
            obtain ⟨j₁, hj₁⟩ := P₁.surj hB
            exact ⟨j₁, by rw [hj₁]; exact hBsub⟩
        · exact Or.inr (Or.inl hpb')
      · exact Or.inl hpa'
    · intro hp
      by_cases hpa' : P₀.X t.unpair.1.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
      · by_cases hpb' : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
        · rcases hp with h | h | ⟨⟨j₀, hj₀⟩, ⟨j₁, hj₁⟩⟩
          · exact absurd hpa' h
          · exact absurd hpb' h
          · have hXint : V₀.mem (P₀.X t.unpair.1.unpair.1 ∩ P₀.X t.unpair.2.unpair.1) :=
              V₀.inter_mem (P₀.mem_X _) (P₀.mem_X _) (P₀.mem_X j₀) hj₀
            have hYint : V₁.mem (P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2) :=
              V₁.inter_mem (P₁.mem_X _) (P₁.mem_X _) (P₁.mem_X j₁) hj₁
            have hXne : P₀.X t.unpair.1.unpair.1 ∩ P₀.X t.unpair.2.unpair.1 ≠ V₀.master :=
              inter_ne_master_left (P₀.mem_X _) hpa'.1
            have hYne : P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2 ≠ V₁.master :=
              inter_ne_master_left (P₁.mem_X _) hpa'.2
            obtain ⟨p₀, hp₀⟩ := P₀.surj hXint
            obtain ⟨p₁, hp₁⟩ := P₁.surj hYint
            refine ⟨Nat.pair p₀ p₁, ?_⟩
            rw [smashEnum_proper (by
                  rw [unpair_pair_fst, unpair_pair_snd, hp₀, hp₁]; exact ⟨hXne, hYne⟩),
              unpair_pair_fst, unpair_pair_snd, hp₀, hp₁, smashEnum_proper hpa',
              smashEnum_proper hpb', prodNbhd.inter]
        · refine ⟨t.unpair.1, ?_⟩
          rw [smashEnum_master (t := t.unpair.2) hpb',
            Set.inter_eq_left.mpr (smashEnum_subset_master t.unpair.1)]
      · refine ⟨t.unpair.2, ?_⟩
        rw [smashEnum_master (t := t.unpair.1) hpa',
          Set.inter_eq_right.mpr (smashEnum_subset_master t.unpair.2)]

@[simp] theorem smashPresentation_X (t : ℕ) :
    (smashPresentation P₀ P₁).X t = smashEnum P₀ P₁ t := rfl

def smashProj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₀ where
  rel W X' := (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨-, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [prodNbhd.inl_preimage] at hsub hsub' ⊢
    exact ⟨hW, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

@[simp] theorem smashProj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (smashProj₀ V₀ V₁).rel W X' ↔ (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

def smashProj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₁ where
  rel W Y' := (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨-, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [prodNbhd.inr_preimage] at hsub hsub' ⊢
    exact ⟨hW, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

@[simp] theorem smashProj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (smashProj₁ V₀ V₁).rel W Y' ↔ (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

def smashPaired {V₂ : NeighborhoodSystem γ} (a : ApproximableMap V₂ V₀)
    (b : ApproximableMap V₂ V₁) : ApproximableMap V₂ (smash V₀ V₁) where
  rel Z W := V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
    (W = prodNbhd V₀.master V₁.master ∨
      ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₂.master_mem, (smash V₀ V₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro Z W₁ W₂ ⟨hZ, hW₁, hd₁⟩ ⟨-, hW₂, hd₂⟩
    have key : W₁ ∩ W₂ = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W₁ ∩ W₂ = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧
          a.rel Z A ∧ b.rel Z B := by
      rcases hd₁ with rfl | ⟨A₁, B₁, rfl, hA₁, hB₁, ha₁, hb₁⟩
      · rw [Set.inter_eq_right.mpr (show W₂ ⊆ prodNbhd V₀.master V₁.master from
          (smash V₀ V₁).sub_master hW₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨A₂, B₂, rfl, hA₂, hB₂, ha₂, hb₂⟩
        · rw [Set.inter_eq_left.mpr (show prodNbhd A₁ B₁ ⊆ prodNbhd V₀.master V₁.master from
            (smash V₀ V₁).sub_master hW₁)]
          exact Or.inr ⟨A₁, B₁, rfl, hA₁, hB₁, ha₁, hb₁⟩
        · rw [prodNbhd.inter]
          exact Or.inr ⟨A₁ ∩ A₂, B₁ ∩ B₂, rfl,
            inter_ne_master_left (a.rel_cod ha₁) hA₁,
            inter_ne_master_left (b.rel_cod hb₁) hB₁,
            a.inter_right ha₁ ha₂, b.inter_right hb₁ hb₂⟩
    refine ⟨hZ, ?_, key⟩
    rcases key with hm | ⟨A, B, hWW, hA, hB, ha, hb⟩
    · rw [hm]; exact (smash V₀ V₁).master_mem
    · rw [hWW]; exact smash_mem_proper (a.rel_cod ha) hA (b.rel_cod hb) hB
  mono := by
    rintro Z Z₂ W W₂ ⟨_, _, hd⟩ hZ₂Z hWW₂ hZ₂mem hW₂mem
    refine ⟨hZ₂mem, hW₂mem, ?_⟩
    rcases hd with rfl | ⟨A, B, rfl, hA, hB, ha, hb⟩
    · left; exact Set.Subset.antisymm ((smash V₀ V₁).sub_master hW₂mem) hWW₂
    · rcases smash_mem_iff.mp hW₂mem with rfl | ⟨A₂, B₂, hA₂, hA₂ne, hB₂, hB₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hAA₂, hBB₂⟩ := prodNbhd.subset_iff.mp hWW₂
        exact Or.inr ⟨A₂, B₂, rfl, hA₂ne, hB₂ne,
          a.mono ha hZ₂Z hAA₂ hZ₂mem hA₂, b.mono hb hZ₂Z hBB₂ hZ₂mem hB₂⟩

@[simp] theorem smashPaired_rel {V₂ : NeighborhoodSystem γ} {a : ApproximableMap V₂ V₀}
    {b : ApproximableMap V₂ V₁} {Z : Set γ} {W : Set (α ⊕ β)} :
    (smashPaired a b).rel Z W ↔ V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
      (W = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B) :=
  Iff.rfl

end Smash
section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

def smashMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (smash V₀ V₁) (smash V₀' V₁') where
  rel W W' := (smash V₀ V₁).mem W ∧ (smash V₀' V₁').mem W' ∧
    (W' = prodNbhd V₀'.master V₁'.master ∨
      ∃ A B A' B', W = prodNbhd A B ∧ W' = prodNbhd A' B' ∧
        A' ≠ V₀'.master ∧ B' ≠ V₁'.master ∧ f.rel A A' ∧ g.rel B B')
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, (smash V₀' V₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have key : W'₁ ∩ W'₂ = prodNbhd V₀'.master V₁'.master ∨
        ∃ A B A' B', W = prodNbhd A B ∧ W'₁ ∩ W'₂ = prodNbhd A' B' ∧
          A' ≠ V₀'.master ∧ B' ≠ V₁'.master ∧ f.rel A A' ∧ g.rel B B' := by
      rcases hd₁ with rfl | ⟨A, B, A'₁, B'₁, hWAB, rfl, hA'₁, hB'₁, hf₁, hg₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ prodNbhd V₀'.master V₁'.master from
          (smash V₀' V₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨A₂, B₂, A'₂, B'₂, hWAB₂, rfl, hA'₂, hB'₂, hf₂, hg₂⟩
        · rw [Set.inter_eq_left.mpr (show prodNbhd A'₁ B'₁ ⊆ prodNbhd V₀'.master V₁'.master from
            (smash V₀' V₁').sub_master hW'₁)]
          exact Or.inr ⟨A, B, A'₁, B'₁, hWAB, rfl, hA'₁, hB'₁, hf₁, hg₁⟩
        · obtain ⟨rfl, rfl⟩ := prodNbhd.injective (hWAB.symm.trans hWAB₂)
          rw [prodNbhd.inter]
          exact Or.inr ⟨A, B, A'₁ ∩ A'₂, B'₁ ∩ B'₂, hWAB, rfl,
            inter_ne_master_left (f.rel_cod hf₁) hA'₁,
            inter_ne_master_left (g.rel_cod hg₁) hB'₁,
            f.inter_right hf₁ hf₂, g.inter_right hg₁ hg₂⟩
    refine ⟨hW, ?_, key⟩
    rcases key with hm | ⟨A, B, A', B', -, hWW', hA', hB', hf, hg⟩
    · rw [hm]; exact (smash V₀' V₁').master_mem
    · rw [hWW']; exact smash_mem_proper (f.rel_cod hf) hA' (g.rel_cod hg) hB'
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨A, B, A', B', rfl, rfl, hA', hB', hf, hg⟩
    · left; exact Set.Subset.antisymm ((smash V₀' V₁').sub_master hW'₂mem) hW'W'₂
    · obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := smash_mem_prodNbhd_form hW₂mem
      obtain ⟨hA₂A, hB₂B⟩ := prodNbhd.subset_iff.mp hW₂W
      rcases smash_mem_iff.mp hW'₂mem with rfl |
        ⟨A'₂, B'₂, hA'₂, hA'₂ne, hB'₂, hB'₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hA'A'₂, hB'B'₂⟩ := prodNbhd.subset_iff.mp hW'W'₂
        exact Or.inr ⟨A₂, B₂, A'₂, B'₂, rfl, rfl, hA'₂ne, hB'₂ne,
          f.mono hf hA₂A hA'A'₂ hA₂ hA'₂, g.mono hg hB₂B hB'B'₂ hB₂ hB'₂⟩

end SmashFunctor

end Smash
section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem smashMap_isComputable (P₀' : ComputablePresentation V₀') (P₁' : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : ComputableMapS P₀.toScott P₀'.toScott f)
    (hg : ComputableMapS P₁.toScott P₁'.toScott g) :
    ComputableMapS (smashPresentation P₀ P₁) (smashPresentation P₀' P₁') (smashMap f g) := by
  constructor
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.1 P₀.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
  have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.2 P₁.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)

  have Hf : REPred (fun t => f.rel (P₀.toScott.X
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.1 P₀.masterIdx)) (P₀'.toScott.X t.unpair.2.unpair.1)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf.out.comp ((heffLp.comp Nat.Primrec.left).pair
        (Nat.Primrec.left.comp Nat.Primrec.right)))
  have Hg : REPred (fun t => g.rel (P₁.toScott.X
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.2 P₁.masterIdx)) (P₁'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg.out.comp ((heffRp.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hJP : RecDecidable (fun t => P₀'.X t.unpair.2.unpair.1 ≠ V₀'.master ∧
      P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master) :=
    ((proper₀_dec P₀').comp (Nat.Primrec.left.comp Nat.Primrec.right)).and
      ((proper₁_dec P₁').comp (Nat.Primrec.right.comp Nat.Primrec.right))
  refine REPred.of_iff (fun t => ?_) ((hJP.not.re).or (hJP.re.and (Hf.and Hg)))
  show (smashMap f g).rel (smashEnum P₀ P₁ t.unpair.1) (smashEnum P₀' P₁' t.unpair.2) ↔ _
  have heq : smashEnum P₀ P₁ t.unpair.1 = prodNbhd
      (P₀.X (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.1 P₀.masterIdx))
      (P₁.X (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.2 P₁.masterIdx)) := smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁ t.unpair.1
  by_cases hJPm : P₀'.X t.unpair.2.unpair.1 ≠ V₀'.master ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master
  · constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨A, B, A', B', hWAB, hW'AB, -, -, hfr, hgr⟩
      · rw [smashEnum_proper hJPm] at hmaster
        exact absurd (prodNbhd.injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hW'AB
        obtain ⟨rfl, rfl⟩ := prodNbhd.injective (heq.symm.trans hWAB)
        obtain ⟨rfl, rfl⟩ := prodNbhd.injective hW'AB
        exact Or.inr ⟨hJPm, hfr, hgr⟩
    · rintro (hnp | ⟨-, hfr, hgr⟩)
      · exact absurd hJPm hnp
      · exact ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) t.unpair.1,
          smashEnum_mem (P₀ := P₀') (P₁ := P₁') t.unpair.2,
          Or.inr ⟨_, _, _, _, heq, smashEnum_proper hJPm, hJPm.1, hJPm.2, hfr, hgr⟩⟩
  · constructor
    · intro _; exact Or.inl hJPm
    · intro _
      exact ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) t.unpair.1,
        smashEnum_mem (P₀ := P₀') (P₁ := P₁') t.unpair.2,
        Or.inl (smashEnum_master hJPm)⟩

end SmashFunctor

theorem smashPaired_isComputable {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁}
    (ha : ComputableMapS P₂.toScott P₀.toScott a)
    (hb : ComputableMapS P₂.toScott P₁.toScott b) :
    ComputableMapS P₂.toScott (smashPresentation P₀ P₁) (smashPaired a b) := by
  constructor
  have Ha : REPred (fun t => a.rel (P₂.toScott.X t.unpair.1) (P₀.toScott.X t.unpair.2.unpair.1)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (ha.out.comp (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)))
  have Hb : REPred (fun t => b.rel (P₂.toScott.X t.unpair.1) (P₁.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hb.out.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hJP : RecDecidable (fun t => P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧
      P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    ((proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.right)).and
      ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right))
  refine REPred.of_iff (fun t => ?_) ((hJP.not.re).or (hJP.re.and (Ha.and Hb)))
  show (smashPaired a b).rel (P₂.X t.unpair.1) (smashEnum P₀ P₁ t.unpair.2) ↔ _
  by_cases hJPm : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
  · constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨A, B, hWAB, -, -, ha', hb'⟩
      · rw [smashEnum_proper hJPm] at hmaster
        exact absurd (prodNbhd.injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hWAB
        obtain ⟨rfl, rfl⟩ := prodNbhd.injective hWAB
        exact Or.inr ⟨hJPm, ha', hb'⟩
    · rintro (hnp | ⟨-, ha', hb'⟩)
      · exact absurd hJPm hnp
      · exact ⟨P₂.mem_X _, smashEnum_mem (P₀ := P₀) (P₁ := P₁) _,
          Or.inr ⟨_, _, smashEnum_proper hJPm, hJPm.1, hJPm.2, ha', hb'⟩⟩
  · constructor
    · intro _; exact Or.inl hJPm
    · intro _
      exact ⟨P₂.mem_X _, smashEnum_mem (P₀ := P₀) (P₁ := P₁) _,
        Or.inl (smashEnum_master hJPm)⟩

theorem smashProj₀_isComputable :
    ComputableMapS (smashPresentation P₀ P₁) P₀.toScott (smashProj₀ V₀ V₁) := by
  constructor
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.1 P₀.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.1 P₀.masterIdx)
      t.unpair.2) := (heffLp.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  show (smashProj₀ V₀ V₁).rel (smashEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2) ↔ _
  simp only [smashProj₀_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨-, -, hsub⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd.inl_preimage] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₀.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd.inl_preimage]
    exact h

theorem smashProj₁_isComputable :
    ComputableMapS (smashPresentation P₀ P₁) P₁.toScott (smashProj₁ V₀ V₁) := by
  constructor
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.2 P₁.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.2 P₁.masterIdx)
      t.unpair.2) := (heffRp.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  show (smashProj₁ V₀ V₁).rel (smashEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2) ↔ _
  simp only [smashProj₁_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨-, -, hsub⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd.inr_preimage] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₁.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd.inr_preimage]
    exact h

theorem smash_isEffectivelyGivenS (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (smash V₀ V₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := h₀; obtain ⟨Q₁⟩ := h₁
  exact ⟨smashPresentation Q₀ Q₁⟩

end Smash

end DomainTheory.NeighbourhoodSystems
