module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive Example61
open NeighborhoodSystem Domain.Recursive ApproximableMap
section
variable {α β γ : Type*}
open Exercise510
section Smash
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
variable {P₀ P₁}
variable (P₀ P₁)
/- concordance: source L4643 EXERCISE 7.15 further constructs effective -/
/-- **Exercise 7.15 — `𝒟₀ ⊗ 𝒟₁` is effectively given (Scott's Definition 7.1).** A bare presentation
of the smash product. The enumeration is classical (re-routing improper products to the master); the
two relations (i),(ii) are choice-free recursively decidable, reducing to the components' relations
on the *effective* indices (relation (i)) and the components' consistency together with properness
tests (relation (ii)). -/
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
    -- effective left/right index of a single code `n`
    have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
        n.unpair.1 P₀.masterIdx) :=
      primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
    have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
        n.unpair.2 P₁.masterIdx) :=
      primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)
    -- reindexings `t ↦ pair (effL t.1) (pair (effL t.2.1) (effL t.2.2))`, ditto for the right factor
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
      smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd_inter, prodNbhd_eq_iff]
  cons_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
    -- `cons(a,b) ↔ ¬proper a ∨ ¬proper b ∨ (P₀.cons(a.1,b.1) ∧ P₁.cons(a.2,b.2))`
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
          · rw [smashEnum_proper hpa', smashEnum_proper hpb', prodNbhd_inter] at hk
            obtain ⟨A, B, hA, _, hkeq⟩ := smashEnum_eq_prodNbhd_mem (P₀ := P₀) (P₁ := P₁) k
            rw [hkeq] at hk
            obtain ⟨hAsub, _⟩ := prodNbhd_subset_iff.mp hk
            obtain ⟨j₀, hj₀⟩ := P₀.surj hA
            exact ⟨j₀, by rw [hj₀]; exact hAsub⟩
          · rw [smashEnum_proper hpa', smashEnum_proper hpb', prodNbhd_inter] at hk
            obtain ⟨A, B, _, hB, hkeq⟩ := smashEnum_eq_prodNbhd_mem (P₀ := P₀) (P₁ := P₁) k
            rw [hkeq] at hk
            obtain ⟨_, hBsub⟩ := prodNbhd_subset_iff.mp hk
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
              smashEnum_proper hpb', prodNbhd_inter]
        · refine ⟨t.unpair.1, ?_⟩
          rw [smashEnum_master (t := t.unpair.2) hpb',
            Set.inter_eq_left.mpr (smashEnum_subset_master t.unpair.1)]
      · refine ⟨t.unpair.2, ?_⟩
        rw [smashEnum_master (t := t.unpair.1) hpa',
          Set.inter_eq_right.mpr (smashEnum_subset_master t.unpair.2)]

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

@[simp] theorem smashPresentation_X (t : ℕ) :
    (smashPresentation P₀ P₁).X t = smashEnum P₀ P₁ t := rfl

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- **The smash projection `p₀ : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀`**, `(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def smashProj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₀ where
  rel W X' := (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨-, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨hW, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

@[simp] theorem smashProj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (smashProj₀ V₀ V₁).rel W X' ↔ (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- **The smash projection `p₁ : 𝒟₀ ⊗ 𝒟₁ → 𝒟₁`**, `(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def smashProj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₁ where
  rel W Y' := (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨-, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨hW, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

@[simp] theorem smashProj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (smashProj₁ V₀ V₁).rel W Y' ↔ (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- **The strict pairing `⟨a, b⟩⊗ : 𝒟₂ → 𝒟₀ ⊗ 𝒟₁`.** Like Theorem 7.4's `paired`, but the smash
collapse forces the image factors to be proper (else the result is the master/bottom of the smash). -/
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
        · rw [prodNbhd_inter]
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
      · obtain ⟨hAA₂, hBB₂⟩ := prodNbhd_subset_iff.mp hWW₂
        exact Or.inr ⟨A₂, B₂, rfl, hA₂ne, hB₂ne,
          a.mono ha hZ₂Z hAA₂ hZ₂mem hA₂, b.mono hb hZ₂Z hBB₂ hZ₂mem hB₂⟩

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

@[simp] theorem smashPaired_rel {V₂ : NeighborhoodSystem γ} {a : ApproximableMap V₂ V₀}
    {b : ApproximableMap V₂ V₁} {Z : Set γ} {W : Set (α ⊕ β)} :
    (smashPaired a b).rel Z W ↔ V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
      (W = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B) :=
  Iff.rfl

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

/-- **Exercise 7.15 — the coalesced sum system `𝒟₀ ⊕ 𝒟₁`** over `Option (α ⊕ β)`: the separated sum
with the improper copies `0Δ₀`, `1Δ₁` deleted. (Generalises `Exercise621.oplusTok` to an arbitrary
carrier.) -/
def osum : NeighborhoodSystem (Option (α ⊕ β)) where
  mem W := W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
    (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y)
  master := sumMaster V₀ V₁
  master_nonempty := ⟨none, none_mem_sumMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact subset_rfl
    · exact inj₀_subset_sumMaster hX
    · exact inj₁_subset_sumMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
        (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y)) → (W : Set (Option (α ⊕ β))).Nonempty := by
      rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · exact ⟨none, none_mem_sumMaster⟩
      · exact inj₀_nonempty (h₀ X hX)
      · exact inj₁_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumMaster_inter_inj₀ hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
      · rw [sumMaster_inter_inj₁ hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₀ hX]; exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
      · rw [inj₀_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₀
        · exact Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ₀ (inj₀_subset_inj₀.mp hZsub),
            inter_ne_master_left hX hXne, rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          exact absurd (hZsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · rw [inj₀_inter_inj₁] at hZsub
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₁ hY]; exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
      · rw [Set.inter_comm, inj₀_inter_inj₁] at hZsub
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [inj₁_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₁
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          exact absurd (hZsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
        · exact Or.inr (Or.inr ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ₁ (inj₁_subset_inj₁.mp hZsub),
            inter_ne_master_right hY hYne, rfl⟩)

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

@[simp] theorem osum_master : (osum h₀ h₁).master = sumMaster V₀ V₁ := rfl

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

open scoped Classical in
/-- **Coalesced-sum enumeration.** Tag `0`/`1`/`≥2`; a tag-0/1 code is its proper left/right copy
when the indexed factor is proper, otherwise it is re-routed to the master (the classical input). -/
noncomputable def osumEnum (t : ℕ) : Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

open scoped Classical in
theorem osumEnum_left {t : ℕ} (h : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) :
    osumEnum P₀ P₁ t = inj₀ (P₀.X t.unpair.2) := ite_eq_left h

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

open scoped Classical in
theorem osumEnum_master {t : ℕ}
    (h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master))
    (h1 : ¬(t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master)) :
    osumEnum P₀ P₁ t = sumMaster V₀ V₁ := by
  unfold osumEnum; rw [ite_eq_right h0, ite_eq_right h1]

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

open scoped Classical in
theorem osumEnum_right {t : ℕ} (h : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) :
    osumEnum P₀ P₁ t = inj₁ (P₁.X t.unpair.2) := by
  have h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) := by
    rintro ⟨hc, -⟩; obtain ⟨h1, -⟩ := h; omega
  unfold osumEnum; rw [ite_eq_right h0, ite_eq_left h]

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

theorem osumEnum_mem (t : ℕ) : (osum h₀ h₁).mem (osumEnum P₀ P₁ t) := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact Or.inr (Or.inl ⟨_, P₀.mem_X _, hL.2, rfl⟩)
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact Or.inr (Or.inr ⟨_, P₁.mem_X _, hR.2, rfl⟩)
    · rw [osumEnum_master hL hR]; exact Or.inl rfl

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

include h₀ h₁ in
theorem osumEnum_nonempty (t : ℕ) : (osumEnum P₀ P₁ t).Nonempty := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact inj₀_nonempty (h₀ _ (P₀.mem_X _))
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact inj₁_nonempty (h₁ _ (P₁.mem_X _))
    · rw [osumEnum_master hL hR]; exact ⟨none, none_mem_sumMaster⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

include h₀ h₁ in
theorem osumEnum_subset_master (t : ℕ) : osumEnum P₀ P₁ t ⊆ sumMaster V₀ V₁ :=
  (osum h₀ h₁).sub_master (osumEnum_mem h₀ h₁ t)

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

/-- **Coalesced left projection `out₀ : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀`**, `W (out₀) X ↔ leftPart W ⊆ X`. -/
def osumOutMap₀ : ApproximableMap (osum h₀ h₁) V₀ where
  rel W X := (osum h₀ h₁).mem W ∧ V₀.mem X ∧ leftPart V₀ W ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨-, hX', hsub'⟩
    refine ⟨hW, V₀.inter_mem hX hX' ?_ (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
    rcases hW with rfl | ⟨A, hA, -, rfl⟩ | ⟨B, hB, -, rfl⟩
    · rw [leftPart_sumMaster]; exact V₀.master_mem
    · rw [leftPart_inj₀]; exact hA
    · rw [leftPart_inj₁ V₀ (h₁ B hB)]; exact V₀.master_mem
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', (leftPart_mono V₀ hW'W).trans (hsub.trans hXX')⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

/-- **Coalesced right projection `out₁ : 𝒟₀ ⊕ 𝒟₁ → 𝒟₁`**. -/
def osumOutMap₁ : ApproximableMap (osum h₀ h₁) V₁ where
  rel W Y := (osum h₀ h₁).mem W ∧ V₁.mem Y ∧ rightPart V₁ W ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W Y Y' ⟨hW, hY, hsub⟩ ⟨-, hY', hsub'⟩
    refine ⟨hW, V₁.inter_mem hY hY' ?_ (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
    rcases hW with rfl | ⟨A, hA, -, rfl⟩ | ⟨B, hB, -, rfl⟩
    · rw [rightPart_sumMaster]; exact V₁.master_mem
    · rw [rightPart_inj₀ V₁ (h₀ A hA)]; exact V₁.master_mem
    · rw [rightPart_inj₁]; exact hB
  mono := by
    rintro W W' Y Y' ⟨_, _, hsub⟩ hW'W hYY' hW' hY'
    exact ⟨hW', hY', (rightPart_mono V₁ hW'W).trans (hsub.trans hYY')⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

/-- **Exercise 7.15 — `𝒟₀ ⊕ 𝒟₁` is effectively given (Scott's Definition 7.1).** -/
noncomputable def osumPresentation : ScottPresentation (osum h₀ h₁) where
  X := osumEnum P₀ P₁
  mem_X := osumEnum_mem h₀ h₁
  surj := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · refine ⟨Nat.pair 2 0, ?_⟩
      rw [osumEnum_master (by rw [unpair_pair_fst]; rintro ⟨h, -⟩; omega)
        (by rw [unpair_pair_fst]; rintro ⟨h, -⟩; omega)]
    · obtain ⟨n, rfl⟩ := P₀.surj hX
      refine ⟨Nat.pair 0 n, ?_⟩
      rw [osumEnum_left (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hXne⟩),
        unpair_pair_snd]
    · obtain ⟨n, rfl⟩ := P₁.surj hY
      refine ⟨Nat.pair 1 n, ?_⟩
      rw [osumEnum_right (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hYne⟩),
        unpair_pair_snd]
  interEq_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
    have hc₀1 : ∀ n, isOne (f₀ n) = 1 ↔ P₀.X n ≠ V₀.master := fun n => by
      rw [isOne_eq_one_iff]; exact (hf₀e n).symm
    have hc₁1 : ∀ n, isOne (f₁ n) = 1 ↔ P₁.X n ≠ V₁.master := fun n => by
      rw [isOne_eq_one_iff]; exact (hf₁e n).symm
    classical
    set r : ℕ → ℕ := fun t =>
      if t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master then Nat.pair 0 t.unpair.2
      else if t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master then Nat.pair 1 t.unpair.2
      else Nat.pair 2 0 with hrdef
    have hr_left : ∀ t, (t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) →
        r t = Nat.pair 0 t.unpair.2 := fun t h => by simp only [hrdef]; exact ite_eq_left h
    have hr_right : ∀ t, ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) →
        (t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) → r t = Nat.pair 1 t.unpair.2 :=
      fun t h0 h1 => by simp only [hrdef]; rw [ite_eq_right h0, ite_eq_left h1]
    have hr_master : ∀ t, ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) →
        ¬(t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) → r t = Nat.pair 2 0 :=
      fun t h0 h1 => by simp only [hrdef]; rw [ite_eq_right h0, ite_eq_right h1]
    have hval : ∀ t, osumEnum P₀ P₁ t = sumEnum P₀ P₁ (r t) := by
      intro t
      by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
      · rw [osumEnum_left hL, hr_left t hL, sumEnum_zero (by rw [unpair_pair_fst]),
          unpair_pair_snd]
      · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
        · rw [osumEnum_right hR, hr_right t hL hR, sumEnum_one (by rw [unpair_pair_fst]),
            unpair_pair_snd]
        · rw [osumEnum_master hL hR, hr_master t hL hR,
            sumEnum_master (by rw [unpair_pair_fst]; decide) (by rw [unpair_pair_fst]; decide)]
    have hbit0 : ∀ v, isOne v = if v = 1 then 1 else 0 := fun v => by
      by_cases h : v = 1
      · rw [ite_eq_left h, h]; rfl
      · rw [ite_eq_right h]; have h1 := isOne_le_one v; have h2 := isOne_eq_one_iff v; omega
    have hrp : Nat.Primrec r := by
      have hchr1 : Nat.Primrec (fun t : ℕ => (1 - t.unpair.1) * isOne (f₀ t.unpair.2)) :=
        primrec_mul₂ (primrec_sub₂ (Nat.Primrec.const 1) Nat.Primrec.left)
          (primrec_isOne.comp (hf₀p.comp Nat.Primrec.right))
      have hchr2 : Nat.Primrec (fun t : ℕ => isOne t.unpair.1 * isOne (f₁ t.unpair.2)) :=
        primrec_mul₂ (primrec_isOne.comp Nat.Primrec.left)
          (primrec_isOne.comp (hf₁p.comp Nat.Primrec.right))
      have hA : Nat.Primrec (fun t : ℕ => Nat.pair 0 t.unpair.2) :=
        (Nat.Primrec.const 0).pair Nat.Primrec.right
      have hB : Nat.Primrec (fun t : ℕ => Nat.pair 1 t.unpair.2) :=
        (Nat.Primrec.const 1).pair Nat.Primrec.right
      have hC : Nat.Primrec (fun _ : ℕ => Nat.pair 2 0) := Nat.Primrec.const _
      have hchr1eq : ∀ t : ℕ, (1 - t.unpair.1) * isOne (f₀ t.unpair.2)
          = if (t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) then 1 else 0 := by
        intro t
        by_cases hc : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
        · rw [ite_eq_left hc]
          have ht0 := hc.1
          have e1 : 1 - t.unpair.1 = 1 := by omega
          rw [e1, (hc₀1 _).mpr hc.2]
        · rw [ite_eq_right hc]
          rcases not_and_or.mp hc with h | h
          · have e1 : 1 - t.unpair.1 = 0 := by omega
            rw [e1, Nat.zero_mul]
          · have e2 : isOne (f₀ t.unpair.2) = 0 := by
              have hle := isOne_le_one (f₀ t.unpair.2)
              by_contra h0; exact h ((hc₀1 _).mp (by omega))
            rw [e2, Nat.mul_zero]
      have hchr2eq : ∀ t : ℕ, isOne t.unpair.1 * isOne (f₁ t.unpair.2)
          = if (t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) then 1 else 0 := by
        intro t
        by_cases hc : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
        · rw [ite_eq_left hc, (by rw [isOne_eq_one_iff]; exact hc.1 : isOne t.unpair.1 = 1),
            (hc₁1 _).mpr hc.2]
        · rw [ite_eq_right hc]
          rcases not_and_or.mp hc with h | h
          · have e1 : isOne t.unpair.1 = 0 := by rw [hbit0]; exact ite_eq_right h
            rw [e1, Nat.zero_mul]
          · have e2 : isOne (f₁ t.unpair.2) = 0 := by
              have hle := isOne_le_one (f₁ t.unpair.2)
              by_contra h0; exact h ((hc₁1 _).mp (by omega))
            rw [e2, Nat.mul_zero]
      refine (primrec_selectFn hchr1 hA (primrec_selectFn hchr2 hB hC)).of_eq (fun t => ?_)
      simp only [hchr1eq, hchr2eq, selectFn_ite, hrdef]
    have hg : Nat.Primrec (fun t => Nat.pair (r t.unpair.1)
        (Nat.pair (r t.unpair.2.unpair.1) (r t.unpair.2.unpair.2))) :=
      (hrp.comp Nat.Primrec.left).pair
        ((hrp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (hrp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_)
      ((sumPresentation (h₀ := h₀) (h₁ := h₁) P₀ P₁).interEq_computable.comp hg)
    have hXeq : ∀ x, (sumPresentation (h₀ := h₀) (h₁ := h₁) P₀ P₁).X x = sumEnum P₀ P₁ x :=
      fun _ => rfl
    simp only [unpair_pair_fst, unpair_pair_snd, hXeq]
    rw [hval t.unpair.1, hval t.unpair.2.unpair.1, hval t.unpair.2.unpair.2]
  cons_computable := by
    have hLa : RecDecidable (fun t => t.unpair.1.unpair.1 = 0
        ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)).and
        ((proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left))
    have hRa : RecDecidable (fun t => t.unpair.1.unpair.1 = 1
        ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)).and
        ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left))
    have hLb : RecDecidable (fun t => t.unpair.2.unpair.1 = 0
        ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)).and
        ((proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hRb : RecDecidable (fun t => t.unpair.2.unpair.1 = 1
        ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)).and
        ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hMca : RecDecidable (fun t => ¬(t.unpair.1.unpair.1 = 0
        ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master)
        ∧ ¬(t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master)) := hLa.not.and hRa.not
    have hMcb : RecDecidable (fun t => ¬(t.unpair.2.unpair.1 = 0
        ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master)
        ∧ ¬(t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master)) := hLb.not.and hRb.not
    have hcons0 : RecDecidable (fun t => ∃ k, P₀.X k ⊆ P₀.X t.unpair.1.unpair.2
        ∩ P₀.X t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₀.cons_computable.comp
        ((Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hcons1 : RecDecidable (fun t => ∃ k, P₁.X k ⊆ P₁.X t.unpair.1.unpair.2
        ∩ P₁.X t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₁.cons_computable.comp
        ((Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_)
      (hMca.or (hMcb.or ((hLa.and (hLb.and hcons0)).or (hRa.and (hRb.and hcons1)))))
    constructor
    · rintro ⟨k, hk⟩
      by_cases hLa' : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
      · by_cases hLb' : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
        · rw [osumEnum_left hLa', osumEnum_left hLb', inj₀_inter] at hk
          refine Or.inr (Or.inr (Or.inl ⟨hLa', hLb', ?_⟩))
          rcases osumEnum_mem h₀ h₁ k with hkm | ⟨Xk, hXk, -, hkeq⟩ | ⟨Yk, hYk, -, hkeq⟩
          · exact absurd (hk (hkm ▸ none_mem_sumMaster)) none_mem_inj₀
          · rw [hkeq, inj₀_subset_inj₀] at hk
            obtain ⟨j, hj⟩ := P₀.surj hXk
            exact ⟨j, by rw [hj]; exact hk⟩
          · rw [hkeq] at hk
            obtain ⟨y0, hy0⟩ := h₁ Yk hYk
            exact absurd (hk (ir_mem_inj₁.mpr hy0)) ir_mem_inj₀
        · by_cases hRb' : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
          · rw [osumEnum_left hLa', osumEnum_right hRb', inj₀_inter_inj₁] at hk
            obtain ⟨m, hm⟩ := osumEnum_nonempty h₀ h₁ k
            exact absurd (hk hm) (Set.notMem_empty m)
          · exact Or.inr (Or.inl ⟨hLb', hRb'⟩)
      · by_cases hRa' : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
        · by_cases hRb' : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hRa', osumEnum_right hRb', inj₁_inter] at hk
            refine Or.inr (Or.inr (Or.inr ⟨hRa', hRb', ?_⟩))
            rcases osumEnum_mem h₀ h₁ k with hkm | ⟨Xk, hXk, -, hkeq⟩ | ⟨Yk, hYk, -, hkeq⟩
            · exact absurd (hk (hkm ▸ none_mem_sumMaster)) none_mem_inj₁
            · rw [hkeq] at hk
              obtain ⟨x0, hx0⟩ := h₀ Xk hXk
              exact absurd (hk (il_mem_inj₀.mpr hx0)) il_mem_inj₁
            · rw [hkeq, inj₁_subset_inj₁] at hk
              obtain ⟨j, hj⟩ := P₁.surj hYk
              exact ⟨j, by rw [hj]; exact hk⟩
          · by_cases hLb' : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
            · rw [osumEnum_right hRa', osumEnum_left hLb', Set.inter_comm,
                inj₀_inter_inj₁] at hk
              obtain ⟨m, hm⟩ := osumEnum_nonempty h₀ h₁ k
              exact absurd (hk hm) (Set.notMem_empty m)
            · exact Or.inr (Or.inl ⟨hLb', hRb'⟩)
        · exact Or.inl ⟨hLa', hRa'⟩
    · intro hp
      rcases hp with hMca' | hMcb' | ⟨hLa', hLb', hc0⟩ | ⟨hRa', hRb', hc1⟩
      · refine ⟨t.unpair.2, ?_⟩
        rw [osumEnum_master hMca'.1 hMca'.2]
        exact Set.subset_inter (osumEnum_subset_master h₀ h₁ t.unpair.2) subset_rfl
      · refine ⟨t.unpair.1, ?_⟩
        rw [osumEnum_master hMcb'.1 hMcb'.2]
        exact Set.subset_inter subset_rfl (osumEnum_subset_master h₀ h₁ t.unpair.1)
      · obtain ⟨j, hj⟩ := hc0
        have hRHSmem : V₀.mem (P₀.X t.unpair.1.unpair.2 ∩ P₀.X t.unpair.2.unpair.2) :=
          V₀.inter_mem (P₀.mem_X _) (P₀.mem_X _) (P₀.mem_X j) hj
        have hRHSne : P₀.X t.unpair.1.unpair.2 ∩ P₀.X t.unpair.2.unpair.2 ≠ V₀.master :=
          inter_ne_master_left (P₀.mem_X _) hLa'.2
        have hjne : P₀.X j ≠ V₀.master := fun he =>
          hRHSne (Set.Subset.antisymm (V₀.sub_master hRHSmem) (he ▸ hj))
        refine ⟨Nat.pair 0 j, ?_⟩
        rw [osumEnum_left (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hjne⟩),
          unpair_pair_snd, osumEnum_left hLa', osumEnum_left hLb', inj₀_inter, inj₀_subset_inj₀]
        exact hj
      · obtain ⟨j, hj⟩ := hc1
        have hRHSmem : V₁.mem (P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2) :=
          V₁.inter_mem (P₁.mem_X _) (P₁.mem_X _) (P₁.mem_X j) hj
        have hRHSne : P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2 ≠ V₁.master :=
          inter_ne_master_right (P₁.mem_X _) hRa'.2
        have hjne : P₁.X j ≠ V₁.master := fun he =>
          hRHSne (Set.Subset.antisymm (V₁.sub_master hRHSmem) (he ▸ hj))
        refine ⟨Nat.pair 1 j, ?_⟩
        rw [osumEnum_right (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hjne⟩),
          unpair_pair_snd, osumEnum_right hRa', osumEnum_right hRb', inj₁_inter, inj₁_subset_inj₁]
        exact hj

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

variable (P₀ P₁)

@[simp] theorem osumPresentation_X (t : ℕ) :
    (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)).X t = osumEnum P₀ P₁ t := rfl

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- The `j`-th fiber **index** of the `D^∞`-code `t`: the `j`-th entry of the coded list, defaulting
to `P.masterIdx` (the master index) beyond the coded length. -/
def iterIdx (t j : ℕ) : ℕ := nthCode t j P.masterIdx

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- The `D^∞`-enumeration: the neighbourhood whose `j`-th fiber is `P.X (iterIdx t j)`. -/
def iterEnum (t : ℕ) : Set (ℕ × α) := {p | p.2 ∈ P.X (iterIdx P t p.1)}

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

@[simp] theorem fiber_iterEnum (t j : ℕ) : fiber (iterEnum P t) j = P.X (iterIdx P t j) := rfl

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- Build, by induction on `N`, a list of fiber indices reproducing `W`'s first `N` fibers. -/
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

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- The coordinate-wise intersection generator: with `s = ⟨j, ⟨n, m⟩⟩`, returns an index of
`X (iterIdx n j) ∩ X (iterIdx m j)` via `P.inter`. -/
def interG (P : ComputablePresentation V) (s : ℕ) : ℕ :=
  P.inter (iterIdx P s.unpair.2.unpair.1 s.unpair.1) (iterIdx P s.unpair.2.unpair.2 s.unpair.1)

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- Beyond the coded length the fiber index defaults to the master: if `t ≤ j` then
`iterIdx t j = masterIdx` (the coded list has length `≤ t`). -/
theorem iterIdx_ge {t j : ℕ} (h : t ≤ j) : iterIdx P t j = P.masterIdx := by
  unfold iterIdx
  rw [nthCode_eq, getD_eq_default_cf]
  exact le_trans (decodeList_length_le t) h

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- **Relation (i) reduces to a bounded coordinate check.** `iterEnum n ∩ iterEnum m = iterEnum k`
iff fiber-wise equality holds for all `j` below `n+m+k` (beyond which every fiber is `Δ`). -/
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

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem iterEnum_mem (t : ℕ) : (iterSys V).mem (iterEnum P t) := by
  refine ⟨fun j => ?_, t, fun j hj => ?_⟩
  · rw [fiber_iterEnum]; exact P.mem_X _
  · rw [fiber_iterEnum, iterIdx_ge hj, P.masterIdx_spec]

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- The `D^∞`-intersection function: tabulate `interG` over the coordinates `0 … n+m-1`. -/
def iterInter (P : ComputablePresentation V) (n m : ℕ) : ℕ :=
  tabCode (interG P) (Nat.pair (n + m) (Nat.pair n m)) (n + m)

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem iterInter_idx_ge {n m j : ℕ} (hj : n + m ≤ j) :
    iterIdx P (iterInter P n m) j = P.masterIdx := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_ge hj]

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem iterInter_idx_lt {n m j : ℕ} (hj : j < n + m) :
    iterIdx P (iterInter P n m) j = P.inter (iterIdx P n j) (iterIdx P m j) := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_lt hj]
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- **Relation (ii) reduces to a bounded coordinate check.** `iterEnum n ∩ iterEnum m` is consistent
iff every coordinate `j < n+m` is consistent in `V`. The witness is `iterInter n m`. -/
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
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

/-- An `osum`-member containing `inj₀ Δ₀` is forced to be the master (the bottom-collapse: the only
proper copy `⊇ inj₀ Δ₀` would need `Δ₀ ⊆ X` with `X ≠ Δ₀`). -/
theorem osum_eq_master_of_inj₀master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₀ V₀.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', -, rfl⟩
  · rfl
  · exact absurd (Set.Subset.antisymm (V₀.sub_master hX') (inj₀_subset_inj₀.mp hsub)) hX'ne
  · obtain ⟨a, ha⟩ := h₀ V₀.master V₀.master_mem
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

/-- **Coalesced left injection `in₀ : 𝒟₀ → 𝒟₀ ⊕ 𝒟₁`**, `X (in₀) W ↔ inj₀ X ⊆ W`. -/
def osumInMap₀ : ApproximableMap V₀ (osum h₀ h₁) where
  rel X W := V₀.mem X ∧ (osum h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (osum h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    refine ⟨hX, ?_, Set.subset_inter hsub hsub'⟩
    by_cases hXm : X = V₀.master
    · subst hXm
      rw [osum_eq_master_of_inj₀master hW hsub, osum_eq_master_of_inj₀master hW' hsub',
        Set.inter_self]
      exact (osum h₀ h₁).master_mem
    · exact (osum h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, hXm, rfl⟩))
        (Set.subset_inter hsub hsub')
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

theorem osum_eq_master_of_inj₁master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₁ V₁.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', -, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
  · rfl
  · obtain ⟨b, hb⟩ := h₁ V₁.master V₁.master_mem
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
  · exact absurd (Set.Subset.antisymm (V₁.sub_master hY') (inj₁_subset_inj₁.mp hsub)) hY'ne

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

/-- **Coalesced right injection `in₁ : 𝒟₁ → 𝒟₀ ⊕ 𝒟₁`**. -/
def osumInMap₁ : ApproximableMap V₁ (osum h₀ h₁) where
  rel Y W := V₁.mem Y ∧ (osum h₀ h₁).mem W ∧ inj₁ Y ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₁.master_mem, (osum h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
  inter_right := by
    rintro Y W W' ⟨hY, hW, hsub⟩ ⟨-, hW', hsub'⟩
    refine ⟨hY, ?_, Set.subset_inter hsub hsub'⟩
    by_cases hYm : Y = V₁.master
    · subst hYm
      rw [osum_eq_master_of_inj₁master hW hsub, osum_eq_master_of_inj₁master hW' hsub',
        Set.inter_self]
      exact (osum h₀ h₁).master_mem
    · exact (osum h₀ h₁).inter_mem hW hW' (Or.inr (Or.inr ⟨Y, hY, hYm, rfl⟩))
        (Set.subset_inter hsub hsub')
  mono := by
    rintro Y Y' W W' ⟨_, _, hsub⟩ hY'Y hWW' hY' hW'
    exact ⟨hY', hW', (inj₁_subset_inj₁.mpr hY'Y).trans (hsub.trans hWW')⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

variable (P₀ P₁)

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)

/-- An `osum`-member `⊆ inj₀ X` is a *proper* left copy. -/
theorem osum_mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (osum h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ X₂ ≠ V₀.master ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, hne, rfl⟩ | ⟨Y₂, hY₂, hne, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, hne, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

end CoalescedFunctor

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

variable (P₀ P₁)

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)

theorem osum_mem_subset_inj₁ {W : Set (Option (α ⊕ β))} {Y : Set β}
    (hW : (osum h₀ h₁).mem W) (hsub : W ⊆ inj₁ Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ Y₂ ≠ V₁.master ∧ W = inj₁ Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, hne, rfl⟩ | ⟨Y₂, hY₂, hne, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
  · exact ⟨Y₂, hY₂, hne, rfl⟩

end CoalescedFunctor

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

variable (P₀ P₁)

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)

/-- **The coalesced sum of two maps `f ⊕ g : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀' ⊕ 𝒟₁'`.** -/
def osumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (osum h₀ h₁) (osum h₀' h₁') where
  rel W W' := (osum h₀ h₁).mem W ∧ (osum h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, (osum h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y')) →
          (osum h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hY'ne, hf⟩ | ⟨_, Y', _, rfl, hY'ne, hg⟩)
      · exact (osum h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, hY'ne, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, hY'ne, rfl⟩)
    have key : W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y') := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hY'₁ne, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hY'₁ne, hg₁⟩
      · have he : sumMaster V₀' V₁' ∩ W'₂ = W'₂ :=
          Set.inter_eq_self_of_subset_right
            ((osum h₀' h₁').sub_master hW'₂ : W'₂ ⊆ sumMaster V₀' V₁')
        rw [he]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hY'₂ne, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hY'₂ne, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hY'₁ne, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl,
            inter_ne_master_left (f.rel_cod hf₁) hY'₁ne, f.inter_right hf₁ hf₂⟩)
        · exact absurd (hWX₁.symm.trans hWY₂)
            (fun h => not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hY'₂ne, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hY'₂ne, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hY'₁ne, hg₁⟩)
        · exact absurd (hWY₁.symm.trans hWX₂)
            (fun h => not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl,
            inter_ne_master_left (g.rel_cod hg₁) hY'₁ne, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hY'ne, hf⟩ | ⟨Y, Y', rfl, rfl, hY'ne, hg⟩
    · left; exact Set.Subset.antisymm ((osum h₀' h₁').sub_master hW'₂mem) hW'W'₂
    · obtain ⟨X₂, hX₂, hX₂ne, rfl⟩ := osum_mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, hY'₂ne, rfl⟩ | ⟨Z'₂, hZ'₂, hZ'₂ne, rfl⟩
      · left; rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl, hY'₂ne,
          f.mono hf hXX₂ (inj₀_subset_inj₀.mp hW'W'₂) hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    · obtain ⟨Y₂, hY₂, hY₂ne, rfl⟩ := osum_mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, hX'₂ne, rfl⟩ | ⟨Y'₂, hY'₂, hY'₂ne, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl, hY'₂ne,
          g.mono hg hYY₂ (inj₁_subset_inj₁.mp hW'W'₂) hY₂ hY'₂⟩)

end CoalescedFunctor

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- Primitive recursivity of `fun w ↦ iterIdx (codeProj w) (w.unpair.1)` for a primrec `codeProj`. -/
theorem primrec_iterIdx_proj {codeProj : ℕ → ℕ} (hc : Nat.Primrec codeProj) :
    Nat.Primrec (fun w => iterIdx P (codeProj w) w.unpair.1) := by
  refine (primrec_nthCode.comp (hc.pair (Nat.Primrec.left.pair
    (Nat.Primrec.const P.masterIdx)))).of_eq (fun w => ?_)
  simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

theorem primrec_interG : Nat.Primrec (interG P) := by
  have hA : Nat.Primrec (fun s => iterIdx P s.unpair.2.unpair.1 s.unpair.1) :=
    primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
  have hB : Nat.Primrec (fun s => iterIdx P s.unpair.2.unpair.2 s.unpair.1) :=
    primrec_iterIdx_proj (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (P.inter_primrec.comp (hA.pair hB)).of_eq (fun s => ?_)
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- **Exercise 7.15 (Scott 1981, PRG-19) — `D^∞` carries a full computable presentation.** Built
choice-free from a presentation `P` of `V`: the enumeration codes finite fiber-index lists, the two
relations reduce to bounded coordinate checks (`RecDecidable.bForall`), and the intersection function
tabulates `P.inter` coordinate-wise. -/
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
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **The smash of two maps `f ⊗ g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀' ⊗ 𝒟₁'`.** -/
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
        · obtain ⟨rfl, rfl⟩ := prodNbhd_injective (hWAB.symm.trans hWAB₂)
          rw [prodNbhd_inter]
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
      obtain ⟨hA₂A, hB₂B⟩ := prodNbhd_subset_iff.mp hW₂W
      rcases smash_mem_iff.mp hW'₂mem with rfl |
        ⟨A'₂, B'₂, hA'₂, hA'₂ne, hB'₂, hB'₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hA'A'₂, hB'B'₂⟩ := prodNbhd_subset_iff.mp hW'W'₂
        exact Or.inr ⟨A₂, B₂, A'₂, B'₂, rfl, rfl, hA'₂ne, hB'₂ne,
          f.mono hf hA₂A hA'A'₂ hA₂ hA'₂, g.mono hg hB₂B hB'B'₂ hB₂ hB'₂⟩

end SmashFunctor

end Smash
end

section
variable {α β γ : Type*}

/-- A full (`inter`-carrying) presentation forgets to a bare one. Hence the project's
`IsEffectivelyGiven` implies Scott's `IsEffectivelyGivenS`. -/
def ComputablePresentation.toScott {V : NeighborhoodSystem α} (P : ComputablePresentation V) :
    ScottPresentation V where
  X := P.X
  mem_X := P.mem_X
  surj := P.surj
  interEq_computable := P.interEq_computable
  cons_computable := P.cons_computable
end

section
variable {α β γ : Type*}

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

end ScottPresentation

open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

@[simp] theorem iterPresentation_X (t : ℕ) : (iterPresentation P).X t = iterEnum P t := rfl

end Iterate
end

section
variable {α β γ : Type*}

theorem NeighborhoodSystem.IsEffectivelyGiven.toS {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.IsEffectivelyGivenS :=
  h.elim fun P => ⟨P.toScott⟩
end

section
variable {α β γ : Type*}
open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)


variable {P}


/-- **Exercise 7.15 (Scott 1981, PRG-19) — the infinite iterate `D^∞` is effectively given.** -/
theorem iterSys_isEffectivelyGiven (e : V.IsEffectivelyGiven) :
    (iterSys V).IsEffectivelyGiven := by
  obtain ⟨Q⟩ := e
  exact ⟨iterPresentation (P := Q)⟩

end Iterate
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable {h₀ h₁}


variable (P₀ P₁)


/-- **`in₀` is computable.** `X⁰ₙ (in₀) (osumEnum m)` decodes to: `m` a proper left copy with
`X⁰ₙ ⊆ X⁰_{m.2}`, or `m` the master (`inj₀` of a proper neighbourhood always sits under the master);
the proper-right case is impossible (`inj₀` of a nonempty set is not `⊆ inj₁`). -/
theorem osumInMap₀_isComputable :
    ComputableMapS P₀.toScott (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) osumInMap₀ := by
  constructor
  have hT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hInc : RecDecidable (fun t => P₀.X t.unpair.1 ⊆ P₀.X t.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₀.incl_computable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT0.and (hP0.and hInc)).or ((hT0.and hP0).not.and (hT1.and hP1).not))).re
  show (osumInMap₀ (h₀ := h₀) (h₁ := h₁)).rel (P₀.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2) ↔ _
  rw [show (osumInMap₀ (h₀ := h₀) (h₁ := h₁)).rel (P₀.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2)
      ↔ inj₀ (P₀.X t.unpair.1) ⊆ osumEnum P₀ P₁ t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨P₀.mem_X _, osumEnum_mem h₀ h₁ _, h⟩⟩]
  by_cases hL : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL, inj₀_subset_inj₀]
    exact ⟨fun h => Or.inl ⟨hL.1, hL.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hL h.1)⟩
  · by_cases hR : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]
      refine ⟨fun h => ?_, fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL)
        (fun h => absurd hR h.2)⟩
      obtain ⟨a, ha⟩ := h₀ _ (P₀.mem_X t.unpair.1)
      exact absurd (h (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rw [osumEnum_master hL hR]
      exact ⟨fun _ => Or.inr ⟨hL, hR⟩, fun _ => inj₀_subset_sumMaster (P₀.mem_X _)⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable {h₀ h₁}


variable (P₀ P₁)


/-- **`in₁` is computable.** Symmetric to `in₀`. -/
theorem osumInMap₁_isComputable :
    ComputableMapS P₁.toScott (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) osumInMap₁ := by
  constructor
  have hT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hInc : RecDecidable (fun t => P₁.X t.unpair.1 ⊆ P₁.X t.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₁.incl_computable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT1.and (hP1.and hInc)).or ((hT0.and hP0).not.and (hT1.and hP1).not))).re
  show (osumInMap₁ (h₀ := h₀) (h₁ := h₁)).rel (P₁.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2) ↔ _
  rw [show (osumInMap₁ (h₀ := h₀) (h₁ := h₁)).rel (P₁.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2)
      ↔ inj₁ (P₁.X t.unpair.1) ⊆ osumEnum P₀ P₁ t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨P₁.mem_X _, osumEnum_mem h₀ h₁ _, h⟩⟩]
  by_cases hL : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb⟩ := h₁ _ (P₁.mem_X t.unpair.1)
      exact absurd (h (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
    · rcases h with ⟨h1, -⟩ | ⟨hn0, -⟩
      · rw [hL.1] at h1; exact absurd h1 (by decide)
      · exact absurd hL hn0
  · by_cases hR : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR, inj₁_subset_inj₁]
      exact ⟨fun h => Or.inl ⟨hR.1, hR.2, h⟩,
        fun h => h.elim (fun h => h.2.2) (fun h => absurd hR h.2)⟩
    · rw [osumEnum_master hL hR]
      exact ⟨fun _ => Or.inr ⟨hL, hR⟩, fun _ => inj₁_subset_sumMaster (P₁.mem_X _)⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable {h₀ h₁}


variable (P₀ P₁)


section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)


/-- **`f ⊕ g` is computable.** The relation `(osumEnum n) (f⊕g) (osumEnum' m)` decodes by tags: `m`
improper (master absorbs), or `m`/`n` both proper left copies with `f`'s r.e. relation, or both
proper right copies with `g`'s. -/
theorem osumMap_isComputable (P₀' : ComputablePresentation V₀') (P₁' : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : ComputableMapS P₀.toScott P₀'.toScott f)
    (hg : ComputableMapS P₁.toScott P₁'.toScott g) :
    ComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁))
      (osumPresentation h₀' h₁' (P₀ := P₀') (P₁ := P₁')) (osumMap h₀' h₁' f g) := by
  constructor
  have mT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have mT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have mP0 : RecDecidable (fun t => P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master) :=
    (proper₀_dec P₀').comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have mP1 : RecDecidable (fun t => P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master) :=
    (proper₁_dec P₁').comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have nT0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have nT1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have nP0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have nP1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have Hf : REPred (fun t => f.rel (P₀.toScott.X t.unpair.1.unpair.2)
      (P₀'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf.out.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have Hg : REPred (fun t => g.rel (P₁.toScott.X t.unpair.1.unpair.2)
      (P₁'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg.out.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hImp : RecDecidable (fun t => ¬(t.unpair.2.unpair.1 = 0 ∧ P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master)
      ∧ ¬(t.unpair.2.unpair.1 = 1 ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master)) :=
    (mT0.and mP0).not.and (mT1.and mP1).not
  refine REPred.of_iff (fun t => ?_)
    ((hImp.re).or ((((mT0.and mP0).and (nT0.and nP0)).re.and Hf).or
      (((mT1.and mP1).and (nT1.and nP1)).re.and Hg)))
  show (osumMap h₀' h₁' f g).rel (osumEnum P₀ P₁ t.unpair.1) (osumEnum P₀' P₁' t.unpair.2) ↔ _
  by_cases hm0 : t.unpair.2.unpair.1 = 0 ∧ P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master
  · rw [osumEnum_left hm0]
    constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨X, Y', hnX, hW'eq, -, hf⟩ | ⟨Y, Y', -, hW'eq, -, -⟩
      · exact absurd hmaster inj₀_ne_sumMaster
      · obtain rfl : Y' = P₀'.X t.unpair.2.unpair.2 := (inj₀_injective hW'eq).symm
        by_cases hn0 : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
        · rw [osumEnum_left hn0] at hnX
          obtain rfl : P₀.X t.unpair.1.unpair.2 = X := inj₀_injective hnX
          exact Or.inr (Or.inl ⟨⟨hm0, hn0⟩, hf⟩)
        · exfalso
          by_cases hn1 : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hn1] at hnX
            obtain ⟨b, hb⟩ := h₁ _ (P₁.mem_X _)
            exact ir_mem_inj₀ (hnX ▸ ir_mem_inj₁.mpr hb)
          · rw [osumEnum_master hn0 hn1] at hnX
            exact none_mem_inj₀ (hnX ▸ none_mem_sumMaster)
      · obtain ⟨a, ha⟩ := h₀' _ (P₀'.mem_X _)
        exact (il_mem_inj₁ (hW'eq ▸ il_mem_inj₀.mpr ha)).elim
    · rintro (himp | ⟨⟨-, hn0⟩, hf⟩ | ⟨⟨hm1, -⟩, -⟩)
      · exact absurd hm0 himp.1
      · exact ⟨osumEnum_mem h₀ h₁ _, Or.inr (Or.inl ⟨_, P₀'.mem_X _, hm0.2, rfl⟩),
          Or.inr (Or.inl ⟨_, _, osumEnum_left hn0, rfl, hm0.2, hf⟩)⟩
      · obtain ⟨he, -⟩ := hm1; rw [hm0.1] at he; exact absurd he (by decide)
  · by_cases hm1 : t.unpair.2.unpair.1 = 1 ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master
    · rw [osumEnum_right hm1]
      constructor
      · rintro ⟨-, -, hd⟩
        rcases hd with hmaster | ⟨X, Y', -, hW'eq, -, -⟩ | ⟨Y, Y', hnY, hW'eq, -, hg⟩
        · exact absurd hmaster inj₁_ne_sumMaster
        · exact absurd hW'eq.symm (inj₀_ne_inj₁_of_nonempty (h₁' _ (P₁'.mem_X _)))
        · obtain rfl : Y' = P₁'.X t.unpair.2.unpair.2 := (inj₁_injective hW'eq).symm
          by_cases hn1 : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hn1] at hnY
            obtain rfl : P₁.X t.unpair.1.unpair.2 = Y := inj₁_injective hnY
            exact Or.inr (Or.inr ⟨⟨hm1, hn1⟩, hg⟩)
          · exfalso
            by_cases hn0 : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
            · rw [osumEnum_left hn0] at hnY
              obtain ⟨a, ha⟩ := h₀ _ (P₀.mem_X _)
              exact il_mem_inj₁ (hnY ▸ il_mem_inj₀.mpr ha)
            · rw [osumEnum_master hn0 hn1] at hnY
              exact none_mem_inj₁ (hnY ▸ none_mem_sumMaster)
      · rintro (himp | ⟨⟨hm0', -⟩, -⟩ | ⟨⟨-, hn1⟩, hg⟩)
        · exact absurd hm1 himp.2
        · obtain ⟨he, -⟩ := hm0'; rw [hm1.1] at he; exact absurd he (by decide)
        · exact ⟨osumEnum_mem h₀ h₁ _, Or.inr (Or.inr ⟨_, P₁'.mem_X _, hm1.2, rfl⟩),
            Or.inr (Or.inr ⟨_, _, osumEnum_right hn1, rfl, hm1.2, hg⟩)⟩
    · rw [osumEnum_master hm0 hm1]
      constructor
      · intro _; exact Or.inl ⟨hm0, hm1⟩
      · intro _
        exact ⟨osumEnum_mem h₀ h₁ _, (osum h₀' h₁').master_mem, Or.inl rfl⟩

end CoalescedFunctor
end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable {h₀ h₁}


variable (P₀ P₁)


/-- **`out₀` is computable.** `(osumEnum n) (out₀) X⁰_m ↔ leftPart (osumEnum n) ⊆ X⁰_m`; the left
part is `X⁰_{n.2}` on a proper left copy and `Δ₀` on a right copy / the master, so the relation is
`incl` against either `n.2` or the master index `k₀` (`X⁰_{k₀} = Δ₀`). -/
theorem osumOutMap₀_isComputable :
    ComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) P₀.toScott osumOutMap₀ := by
  constructor
  obtain ⟨k0, hk0⟩ := P₀.surj V₀.master_mem
  have hT0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have hIncL : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ⊆ P₀.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₀.incl_computable.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hIncM : RecDecidable (fun t => V₀.master ⊆ P₀.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd, hk0])
      (P₀.incl_computable.comp ((Nat.Primrec.const k0).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT0.and (hP0.and hIncL)).or ((hT0.and hP0).not.and hIncM))).re
  show (osumOutMap₀ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2) ↔ _
  rw [show (osumOutMap₀ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2)
      ↔ leftPart V₀ (osumEnum P₀ P₁ t.unpair.1) ⊆ P₀.X t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨osumEnum_mem h₀ h₁ _, P₀.mem_X _, h⟩⟩]
  by_cases hL : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL, leftPart_inj₀]
    exact ⟨fun h => Or.inl ⟨hL.1, hL.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hL h.1)⟩
  · by_cases hR : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _))]
      exact ⟨fun h => Or.inr ⟨hL, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL) (fun h => h.2)⟩
    · rw [osumEnum_master hL hR, leftPart_sumMaster]
      exact ⟨fun h => Or.inr ⟨hL, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL) (fun h => h.2)⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable {h₀ h₁}


variable (P₀ P₁)


/-- **`out₁` is computable.** Symmetric to `out₀` via `rightPart`. -/
theorem osumOutMap₁_isComputable :
    ComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) P₁.toScott osumOutMap₁ := by
  constructor
  obtain ⟨k1, hk1⟩ := P₁.surj V₁.master_mem
  have hT1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have hIncR : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ⊆ P₁.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₁.incl_computable.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hIncM : RecDecidable (fun t => V₁.master ⊆ P₁.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd, hk1])
      (P₁.incl_computable.comp ((Nat.Primrec.const k1).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT1.and (hP1.and hIncR)).or ((hT1.and hP1).not.and hIncM))).re
  show (osumOutMap₁ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2) ↔ _
  rw [show (osumOutMap₁ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2)
      ↔ rightPart V₁ (osumEnum P₀ P₁ t.unpair.1) ⊆ P₁.X t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨osumEnum_mem h₀ h₁ _, P₁.mem_X _, h⟩⟩]
  by_cases hR : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
  · rw [osumEnum_right hR, rightPart_inj₁]
    exact ⟨fun h => Or.inl ⟨hR.1, hR.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hR h.1)⟩
  · by_cases hL : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
    · rw [osumEnum_left hL, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _))]
      exact ⟨fun h => Or.inr ⟨hR, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hR) (fun h => h.2)⟩
    · rw [osumEnum_master hL hR, rightPart_sumMaster]
      exact ⟨fun h => Or.inr ⟨hR, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hR) (fun h => h.2)⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


include h₀ h₁ in
/-- **Exercise 7.15 (Scott 1981, PRG-19) — the coalesced sum `𝒟₀ ⊕ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem osum_isEffectivelyGivenS (e₀ : V₀.IsEffectivelyGiven) (e₁ : V₁.IsEffectivelyGiven) :
    (osum h₀ h₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := e₀; obtain ⟨Q₁⟩ := e₁
  exact ⟨osumPresentation h₀ h₁ (P₀ := Q₀) (P₁ := Q₁)⟩

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


theorem osum_mem_iff {W : Set (Option (α ⊕ β))} :
    (osum h₀ h₁).mem W ↔ W = sumMaster V₀ V₁ ∨
      (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
      (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y) := Iff.rfl

end Coalesced
end

section
variable {α β γ : Type*}
open Exercise510

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
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable (P₀ P₁)


section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **`f ⊗ g` is computable.** Writing each smash code via its *effective* product index
(`smashEnum_eq_eff`), the relation `(smashEnum n) (f⊗g) (smashEnum' m)` decodes to: `m` improper
(the codomain master absorbs everything), or `m` proper together with `f`'s and `g`'s r.e. relations
on the effective coordinate indices. R.e.-ness then follows from `hf`, `hg`, the codomain properness
deciders, and closure of r.e. predicates under `∨`/`∧`/primitive-recursive substitution. -/
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
  -- `f`'s r.e. relation on `(effL n, m.1)`; `g`'s on `(effR n, m.2)`
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
        exact absurd (prodNbhd_injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hW'AB
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective (heq.symm.trans hWAB)
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective hW'AB
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
end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable (P₀ P₁)


/-- **The strict pairing `⟨a, b⟩⊗` is computable.** `Zₙ ⟨a,b⟩⊗ (smashEnum m) ↔` either `m` improper
(the codomain master absorbs) or `m` proper together with `a`'s and `b`'s r.e. relations on the
(raw) codomain coordinate indices — an `∨`/`∧` of r.e. predicates and the codomain properness tests.
No effective-index bridge is needed: the proper branch reads `smashEnum`'s raw factors directly. -/
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
        exact absurd (prodNbhd_injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hWAB
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective hWAB
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

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable (P₀ P₁)


/-- **The smash projection `p₀` is computable.** `(smashEnum n) p₀ X⁰_m ↔ X⁰_{effL n} ⊆ X⁰_m`
(`smashEnum_eq_eff` rewrites `Sum.inl ⁻¹' (smashEnum n)` to the effective left factor), a recursive
slice of `incl_computable`. -/
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
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inl_preimage_prodNbhd] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₀.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inl_preimage_prodNbhd]
    exact h

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable (P₀ P₁)


/-- **The smash projection `p₁` is computable.** Symmetric to `smashProj₀_isComputable`, using the
effective right factor `Sum.inr ⁻¹' (smashEnum n) = X¹_{effR n}`. -/
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
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inr_preimage_prodNbhd] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₁.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inr_preimage_prodNbhd]
    exact h

end Smash
end

section
variable {α β γ : Type*}
open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable (P₀ P₁)


/-- **Exercise 7.15 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem smash_isEffectivelyGivenS (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (smash V₀ V₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := h₀; obtain ⟨Q₁⟩ := h₁
  exact ⟨smashPresentation Q₀ Q₁⟩

end Smash
end

section
set_option linter.unusedVariables false

theorem example_715.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X)
      (h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.osum α β V₀ V₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.Exercise510.smash α β V₀ V₁)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X)
      (h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.osum α β V₀ V₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.Exercise510.smash α β V₀ V₁))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X)
      (h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.osum α β V₀ V₁ h₀ h₁))
    @DomainTheory.NeighbourhoodSystems.iterSys_isEffectivelyGiven
    @DomainTheory.NeighbourhoodSystems.osum_isEffectivelyGivenS)
  @DomainTheory.NeighbourhoodSystems.smash_isEffectivelyGivenS
end

namespace Exercise718
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}

end
end Exercise718
end DomainTheory.NeighbourhoodSystems
end
