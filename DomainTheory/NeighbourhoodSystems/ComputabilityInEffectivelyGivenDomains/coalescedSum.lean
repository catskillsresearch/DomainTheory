module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.scottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.smashEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap SmashProduct

variable {α β γ α' β' : Type*}

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

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

@[simp] theorem osum_master : (osum h₀ h₁).master = sumMaster V₀ V₁ := rfl

end Coalesced
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

open scoped Classical in

noncomputable def osumEnum (t : ℕ) : Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

end Coalesced
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

open scoped Classical in
theorem osumEnum_left {t : ℕ} (h : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) :
    osumEnum P₀ P₁ t = inj₀ (P₀.X t.unpair.2) := ite_eq_left h

open scoped Classical in
theorem osumEnum_master {t : ℕ}
    (h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master))
    (h1 : ¬(t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master)) :
    osumEnum P₀ P₁ t = sumMaster V₀ V₁ := by
  unfold osumEnum; rw [ite_eq_right h0, ite_eq_right h1]

open scoped Classical in
theorem osumEnum_right {t : ℕ} (h : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) :
    osumEnum P₀ P₁ t = inj₁ (P₁.X t.unpair.2) := by
  have h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) := by
    rintro ⟨hc, -⟩; obtain ⟨h1, -⟩ := h; omega
  unfold osumEnum; rw [ite_eq_right h0, ite_eq_left h]

theorem osumEnum_mem (t : ℕ) : (osum h₀ h₁).mem (osumEnum P₀ P₁ t) := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact Or.inr (Or.inl ⟨_, P₀.mem_X _, hL.2, rfl⟩)
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact Or.inr (Or.inr ⟨_, P₁.mem_X _, hR.2, rfl⟩)
    · rw [osumEnum_master hL hR]; exact Or.inl rfl

include h₀ h₁ in
theorem osumEnum_nonempty (t : ℕ) : (osumEnum P₀ P₁ t).Nonempty := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact inj₀_nonempty (h₀ _ (P₀.mem_X _))
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact inj₁_nonempty (h₁ _ (P₁.mem_X _))
    · rw [osumEnum_master hL hR]; exact ⟨none, none_mem_sumMaster⟩

include h₀ h₁ in
theorem osumEnum_subset_master (t : ℕ) : osumEnum P₀ P₁ t ⊆ sumMaster V₀ V₁ :=
  (osum h₀ h₁).sub_master (osumEnum_mem h₀ h₁ t)

end Coalesced
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

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
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

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
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

theorem osum_eq_master_of_inj₀master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₀ V₀.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', -, rfl⟩
  · rfl
  · exact absurd (Set.Subset.antisymm (V₀.sub_master hX') (inj₀_subset_inj₀.mp hsub)) hX'ne
  · obtain ⟨a, ha⟩ := h₀ V₀.master V₀.master_mem
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁

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

theorem osum_eq_master_of_inj₁master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₁ V₁.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', -, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
  · rfl
  · obtain ⟨b, hb⟩ := h₁ V₁.master V₁.master_mem
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
  · exact absurd (Set.Subset.antisymm (V₁.sub_master hY') (inj₁_subset_inj₁.mp hsub)) hY'ne

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

theorem osum_mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (osum h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ X₂ ≠ V₀.master ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, hne, rfl⟩ | ⟨Y₂, hY₂, hne, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, hne, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

end CoalescedFunctor

end Coalesced
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
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

variable (P₀ P₁)

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
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

include h₀ h₁ in

theorem osum_isEffectivelyGivenS (e₀ : V₀.IsEffectivelyGiven) (e₁ : V₁.IsEffectivelyGiven) :
    (osum h₀ h₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := e₀; obtain ⟨Q₁⟩ := e₁
  exact ⟨osumPresentation h₀ h₁ (P₀ := Q₀) (P₁ := Q₁)⟩

end Coalesced
section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

theorem osum_mem_iff {W : Set (Option (α ⊕ β))} :
    (osum h₀ h₁).mem W ↔ W = sumMaster V₀ V₁ ∨
      (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
      (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y) := Iff.rfl

end Coalesced

end DomainTheory.NeighbourhoodSystems
