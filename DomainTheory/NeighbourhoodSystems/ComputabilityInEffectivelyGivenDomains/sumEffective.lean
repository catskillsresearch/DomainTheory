module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sumSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.inducedMaps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap

section
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

def sumEnum (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (t : ℕ) :
    Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

end Sum

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

@[simp] theorem sumEnum_zero {t : ℕ} (h : t.unpair.1 = 0) :
    sumEnum P₀ P₁ t = inj₀ (P₀.X t.unpair.2) := by unfold sumEnum; rw [ite_eq_left h]

@[simp] theorem sumEnum_one {t : ℕ} (h : t.unpair.1 = 1) :
    sumEnum P₀ P₁ t = inj₁ (P₁.X t.unpair.2) := by
  have h0 : t.unpair.1 ≠ 0 := by omega
  unfold sumEnum; rw [ite_eq_right h0, ite_eq_left h]

theorem inj₀_eq_iff {A B : Set α} : (inj₀ A : Set (Option (α ⊕ β))) = inj₀ B ↔ A = B :=
  ⟨inj₀_injective, fun h => h ▸ rfl⟩

theorem inj₀_eq_inj₁_elim {A : Set α} {B : Set β} (hA : A.Nonempty)
    (h : (inj₀ A : Set (Option (α ⊕ β))) = inj₁ B) : False := by
  obtain ⟨a, ha⟩ := hA; exact il_mem_inj₁ (h ▸ il_mem_inj₀.mpr ha)

theorem inj₀_ne_inj₁_of_nonempty {A : Set α} {B : Set β} (hB : B.Nonempty) :
    (inj₀ A : Set (Option (α ⊕ β))) ≠ inj₁ B := by
  rintro h; obtain ⟨b, hb⟩ := hB
  exact ir_mem_inj₀ (h.symm ▸ ir_mem_inj₁.mpr hb)

theorem inj₀_ne_sumMaster {A : Set α} : (inj₀ A : Set (Option (α ⊕ β))) ≠ sumMaster V₀ V₁ :=
  fun h => none_mem_inj₀ (h.symm ▸ none_mem_sumMaster)

theorem inj₁_eq_iff {A B : Set β} : (inj₁ A : Set (Option (α ⊕ β))) = inj₁ B ↔ A = B :=
  ⟨inj₁_injective, fun h => h ▸ rfl⟩

theorem inj₁_ne_sumMaster {B : Set β} : (inj₁ B : Set (Option (α ⊕ β))) ≠ sumMaster V₀ V₁ :=
  fun h => none_mem_inj₁ (h.symm ▸ none_mem_sumMaster)

theorem recDec_setEq₀ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    RecDecidable (fun u => P₀.X (f u) = P₀.X (g u)) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  refine RecDecidable.of_iff (fun u => ?_) ((hincl.comp (hf.pair hg)).and (hincl.comp (hg.pair hf)))
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2⟩

theorem recDec_setEq₁ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    RecDecidable (fun u => P₁.X (f u) = P₁.X (g u)) := by
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  refine RecDecidable.of_iff (fun u => ?_) ((hincl.comp (hf.pair hg)).and (hincl.comp (hg.pair hf)))
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2⟩

theorem sumEnum_master {t : ℕ} (h0 : t.unpair.1 ≠ 0) (h1 : t.unpair.1 ≠ 1) :
    sumEnum P₀ P₁ t = sumMaster V₀ V₁ := by unfold sumEnum; rw [ite_eq_right h0, ite_eq_right h1]

theorem sumEnum_mem (t : ℕ) : (sum V₀ V₁ h₀ h₁).mem (sumEnum P₀ P₁ t) := by
  unfold sumEnum
  split
  · exact Or.inr (Or.inl ⟨_, P₀.mem_X _, rfl⟩)
  · split
    · exact Or.inr (Or.inr ⟨_, P₁.mem_X _, rfl⟩)
    · exact Or.inl rfl

include h₀ h₁ in
theorem sumEnum_nonempty (t : ℕ) : (sumEnum P₀ P₁ t).Nonempty := by
  unfold sumEnum
  split
  · exact inj₀_nonempty (h₀ _ (P₀.mem_X _))
  · split
    · exact inj₁_nonempty (h₁ _ (P₁.mem_X _))
    · exact ⟨none, none_mem_sumMaster⟩

theorem sumEnum_subset_sumMaster (n : ℕ) :
    sumEnum P₀ P₁ n ⊆ sumMaster V₀ V₁ := by
  unfold sumEnum
  split
  · exact inj₀_subset_sumMaster (P₀.mem_X _)
  · split
    · exact inj₁_subset_sumMaster (P₁.mem_X _)
    · exact subset_rfl

theorem sumEnum_inter_sumMaster (n : ℕ) :
    sumEnum P₀ P₁ n ∩ sumMaster V₀ V₁ = sumEnum P₀ P₁ n :=
  Set.inter_eq_left.mpr (sumEnum_subset_sumMaster n)

theorem sumMaster_inter_sumEnum (m : ℕ) :
    sumMaster V₀ V₁ ∩ sumEnum P₀ P₁ m = sumEnum P₀ P₁ m :=
  Set.inter_eq_right.mpr (sumEnum_subset_sumMaster m)

end Sum

theorem tag_trichotomy (n : ℕ) : n = 0 ∨ n = 1 ∨ (n ≠ 0 ∧ n ≠ 1) := by
  have h_dec : (n ≠ 0) ∨ (n = 0) := by
    by_cases h : n = 0
    · exact Or.inr h
    · exact Or.inl h
  rcases h_dec with h | h
  · have h'_dec : (n ≠ 1) ∨ (n = 1) := by
      by_cases h' : n = 1
      · exact Or.inr h'
      · exact Or.inl h'
    rcases h'_dec with h' | h'
    · exact Or.inr (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl h')
  · exact Or.inl h

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

include h₁ in

theorem sumEnum_eq_iff (x y : ℕ) :
    sumEnum P₀ P₁ x = sumEnum P₀ P₁ y ↔
      ((x.unpair.1 ≠ 0 ∧ x.unpair.1 ≠ 1) ∧ (y.unpair.1 ≠ 0 ∧ y.unpair.1 ≠ 1))
        ∨ (((x.unpair.1 = 0 ∧ y.unpair.1 = 0) ∧ P₀.X x.unpair.2 = P₀.X y.unpair.2)
          ∨ ((x.unpair.1 = 1 ∧ y.unpair.1 = 1) ∧ P₁.X x.unpair.2 = P₁.X y.unpair.2)) := by
  rcases tag_trichotomy x.unpair.1 with hx | hx | ⟨hx0, hx1⟩ <;>
    rcases tag_trichotomy y.unpair.1 with hy | hy | ⟨hy0, hy1⟩
  ·
    rw [sumEnum_zero hx, sumEnum_zero hy, inj₀_eq_iff]
    constructor
    · intro he; exact Or.inr (Or.inl ⟨⟨hx, hy⟩, he⟩)
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨_, he⟩ | ⟨⟨e1, e2⟩, _⟩)
      · exfalso; omega
      · exact he
      · exfalso; omega
  ·
    rw [sumEnum_zero hx, sumEnum_one hy]
    constructor
    · intro h; exact absurd h (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  ·
    rw [sumEnum_zero hx, sumEnum_master hy0 hy1]
    constructor
    · intro h; exact absurd h inj₀_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  ·
    rw [sumEnum_one hx, sumEnum_zero hy]
    constructor
    · intro h; exact absurd h.symm (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  ·
    rw [sumEnum_one hx, sumEnum_one hy, inj₁_eq_iff]
    constructor
    · intro he; exact Or.inr (Or.inr ⟨⟨hx, hy⟩, he⟩)
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨_, he⟩)
      · exfalso; omega
      · exfalso; omega
      · exact he
  ·
    rw [sumEnum_one hx, sumEnum_master hy0 hy1]
    constructor
    · intro h; exact absurd h inj₁_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  ·
    rw [sumEnum_master hx0 hx1, sumEnum_zero hy]
    constructor
    · intro h; exact absurd h.symm inj₀_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  ·
    rw [sumEnum_master hx0 hx1, sumEnum_one hy]
    constructor
    · intro h; exact absurd h.symm inj₁_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  ·
    rw [sumEnum_master hx0 hx1, sumEnum_master hy0 hy1]
    exact ⟨fun _ => Or.inl ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, fun _ => rfl⟩

include h₁ in

theorem eqSEdec :
    RecDecidable (fun u => sumEnum P₀ P₁ u.unpair.1 = sumEnum P₀ P₁ u.unpair.2) := by
  have hX0 : RecDecidable (fun u => u.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hX1 : RecDecidable (fun u => u.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hY0 : RecDecidable (fun u => u.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hY1 : RecDecidable (fun u => u.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hE0 : RecDecidable (fun u => P₀.X u.unpair.1.unpair.2 = P₀.X u.unpair.2.unpair.2) :=
    recDec_setEq₀ (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.right.comp Nat.Primrec.right)
  have hE1 : RecDecidable (fun u => P₁.X u.unpair.1.unpair.2 = P₁.X u.unpair.2.unpair.2) :=
    recDec_setEq₁ (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.right.comp Nat.Primrec.right)
  exact RecDecidable.of_iff (fun u => sumEnum_eq_iff (h₁ := h₁) u.unpair.1 u.unpair.2)
    (((hX0.not.and hX1.not).and (hY0.not.and hY1.not)).or
      (((hX0.and hY0).and hE0).or ((hX1.and hY1).and hE1)))

include h₀ h₁

def sumPresentation (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputablePresentation (sum V₀ V₁ h₀ h₁) where
  X := sumEnum P₀ P₁
  mem_X t := sumEnum_mem t
  surj := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact ⟨Nat.pair 2 0, sumEnum_master (by rw [unpair_pair_fst]; decide)
        (by rw [unpair_pair_fst]; decide)⟩
    · obtain ⟨n, rfl⟩ := P₀.surj hX
      exact ⟨Nat.pair 0 n, by rw [sumEnum_zero (by rw [unpair_pair_fst]), unpair_pair_snd]⟩
    · obtain ⟨n, rfl⟩ := P₁.surj hY
      exact ⟨Nat.pair 1 n, by rw [sumEnum_one (by rw [unpair_pair_fst]), unpair_pair_snd]⟩
  interEq_computable := by
    have hMK : RecDecidable (fun t => sumEnum P₀ P₁ t.unpair.2.unpair.1
        = sumEnum P₀ P₁ t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) ((eqSEdec (P₀ := P₀) (P₁ := P₁) (h₁ := h₁)).comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hNK : RecDecidable (fun t => sumEnum P₀ P₁ t.unpair.1
        = sumEnum P₀ P₁ t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) ((eqSEdec (P₀ := P₀) (P₁ := P₁) (h₁ := h₁)).comp
        (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hA0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
      RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
    have hA1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
      RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
    have hB0 : RecDecidable (fun t => t.unpair.2.unpair.1.unpair.1 = 0) :=
      RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)
    have hB1 : RecDecidable (fun t => t.unpair.2.unpair.1.unpair.1 = 1) :=
      RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.const 1)
    have hC0 : RecDecidable (fun t => t.unpair.2.unpair.2.unpair.1 = 0) :=
      RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)
    have hC1 : RecDecidable (fun t => t.unpair.2.unpair.2.unpair.1 = 1) :=
      RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
        (Nat.Primrec.const 1)
    have hg : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2
        (Nat.pair t.unpair.2.unpair.1.unpair.2 t.unpair.2.unpair.2.unpair.2)) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair
        ((Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    have hIE0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ∩ P₀.X t.unpair.2.unpair.1.unpair.2
        = P₀.X t.unpair.2.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₀.interEq_computable.comp hg)
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hIE1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.1.unpair.2
        = P₁.X t.unpair.2.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₁.interEq_computable.comp hg)
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_)
      (((hA0.not.and hA1.not).and hMK).or
        (((hB0.not.and hB1.not).and hNK).or
          ((((hA0.and hB0).and hC0).and hIE0).or
            (((hA1.and hB1).and hC1).and hIE1))))
    dsimp only
    rcases tag_trichotomy t.unpair.1.unpair.1 with hna | hna | ⟨hna0, hna1⟩
    · rcases tag_trichotomy t.unpair.2.unpair.1.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
      ·
        rw [sumEnum_zero hna, sumEnum_zero hnb, inj₀_inter]
        rcases tag_trichotomy t.unpair.2.unpair.2.unpair.1 with hnc | hnc | ⟨hnc0, hnc1⟩
        · rw [sumEnum_zero hnc, inj₀_eq_iff]
          constructor
          · intro h; exact Or.inr (Or.inr (Or.inl ⟨⟨⟨hna, hnb⟩, hnc⟩, h⟩))
          · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨_, _⟩, _⟩, h⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
            · exfalso; omega
            · exfalso; omega
            · exact h
            · exfalso; omega
        · rw [sumEnum_one hnc]
          constructor
          · intro h; exact absurd h (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
          · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨_, _⟩, e3⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
        · rw [sumEnum_master hnc0 hnc1]
          constructor
          · intro h; exact absurd h inj₀_ne_sumMaster
          · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨_, _⟩, e3⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
      ·
        rw [sumEnum_zero hna, sumEnum_one hnb, inj₀_inter_inj₁]
        constructor
        · intro h
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) t.unpair.2.unpair.2
          rw [← h] at hx
          exact absurd hx (Set.notMem_empty x)
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
      ·
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        constructor
        · intro h; exact Or.inr (Or.inl ⟨⟨hnb0, hnb1⟩, h⟩)
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨_, h⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
          · exfalso; omega
          · exact h
          · exfalso; omega
          · exfalso; omega
    · rcases tag_trichotomy t.unpair.2.unpair.1.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
      ·
        rw [sumEnum_one hna, sumEnum_zero hnb, Set.inter_comm, inj₀_inter_inj₁]
        constructor
        · intro h
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) t.unpair.2.unpair.2
          rw [← h] at hx
          exact absurd hx (Set.notMem_empty x)
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩) <;> exfalso <;> omega
      ·
        rw [sumEnum_one hna, sumEnum_one hnb, inj₁_inter]
        rcases tag_trichotomy t.unpair.2.unpair.2.unpair.1 with hnc | hnc | ⟨hnc0, hnc1⟩
        · rw [sumEnum_zero hnc]
          constructor
          · intro h; exact (inj₀_eq_inj₁_elim (h₀ _ (P₀.mem_X _)) h.symm).elim
          · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨_, _⟩, e3⟩, _⟩) <;> exfalso <;> omega
        · rw [sumEnum_one hnc, inj₁_eq_iff]
          constructor
          · intro h; exact Or.inr (Or.inr (Or.inr ⟨⟨⟨hna, hnb⟩, hnc⟩, h⟩))
          · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨_, _⟩, _⟩, h⟩)
            · exfalso; omega
            · exfalso; omega
            · exfalso; omega
            · exact h
        · rw [sumEnum_master hnc0 hnc1]
          constructor
          · intro h; exact absurd h inj₁_ne_sumMaster
          · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨_, _⟩, e3⟩, _⟩) <;> exfalso <;> omega
      ·
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        constructor
        · intro h; exact Or.inr (Or.inl ⟨⟨hnb0, hnb1⟩, h⟩)
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨_, h⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩)
          · exfalso; omega
          · exact h
          · exfalso; omega
          · exfalso; omega
    ·
      rw [sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]
      constructor
      · intro h; exact Or.inl ⟨⟨hna0, hna1⟩, h⟩
      · rintro (⟨_, h⟩ | ⟨⟨e1, e2⟩, h⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
        · exact h
        · rw [sumEnum_master e1 e2]; exact h
        · exfalso; omega
        · exfalso; omega
  cons_computable := by
    have hA0 : RecDecidable (fun s => s.unpair.1.unpair.1 = 0) :=
      RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
    have hA1 : RecDecidable (fun s => s.unpair.1.unpair.1 = 1) :=
      RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
    have hB0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
      RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
    have hB1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
      RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
    have hgc : Nat.Primrec (fun s => Nat.pair s.unpair.1.unpair.2 s.unpair.2.unpair.2) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
    have hC0 : RecDecidable (fun s => ∃ k, P₀.X k ⊆ P₀.X s.unpair.1.unpair.2 ∩ P₀.X s.unpair.2.unpair.2)
        := by
      refine RecDecidable.of_iff (fun s => ?_) (P₀.cons_computable.comp hgc)
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hC1 : RecDecidable (fun s => ∃ k, P₁.X k ⊆ P₁.X s.unpair.1.unpair.2 ∩ P₁.X s.unpair.2.unpair.2)
        := by
      refine RecDecidable.of_iff (fun s => ?_) (P₁.cons_computable.comp hgc)
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun s => ?_)
      ((hA0.not.and hA1.not).or
        ((hB0.not.and hB1.not).or
          (((hA0.and hB0).and hC0).or ((hA1.and hB1).and hC1))))
    dsimp only
    rcases tag_trichotomy s.unpair.1.unpair.1 with hna | hna | ⟨hna0, hna1⟩
    · rcases tag_trichotomy s.unpair.2.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
      ·
        rw [sumEnum_zero hna, sumEnum_zero hnb, inj₀_inter]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨X₂, hX₂mem, hX₂eq⟩ := mem_subset_inj₀ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
          obtain ⟨j, hj⟩ := P₀.surj hX₂mem
          refine Or.inr (Or.inr (Or.inl ⟨⟨hna, hnb⟩, j, ?_⟩))
          rw [hj]
          rw [hX₂eq] at hk
          exact inj₀_subset_inj₀.mp hk
        · rintro (⟨e1, _⟩ | ⟨e1, _⟩ | ⟨⟨_, _⟩, j, hj⟩ | ⟨⟨e1, _⟩, _⟩)
          · exfalso; omega
          · exfalso; omega
          · refine ⟨Nat.pair 0 j, ?_⟩
            rw [sumEnum_zero (by rw [unpair_pair_fst]), unpair_pair_snd]
            exact inj₀_subset_inj₀.mpr hj
          · exfalso; omega
      ·
        rw [sumEnum_zero hna, sumEnum_one hnb, inj₀_inter_inj₁]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
          exact absurd (hk hx) (Set.notMem_empty x)
        · rintro (⟨e1, _⟩ | ⟨_, e2⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨e1, _⟩, _⟩) <;> exfalso <;> omega
      ·
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        exact ⟨fun _ => Or.inr (Or.inl ⟨hnb0, hnb1⟩), fun _ => ⟨s.unpair.1, subset_rfl⟩⟩
    · rcases tag_trichotomy s.unpair.2.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
      ·
        rw [sumEnum_one hna, sumEnum_zero hnb, Set.inter_comm, inj₀_inter_inj₁]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
          exact absurd (hk hx) (Set.notMem_empty x)
        · rintro (⟨_, e2⟩ | ⟨e1, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨_, e2⟩, _⟩) <;> exfalso <;> omega
      ·
        rw [sumEnum_one hna, sumEnum_one hnb, inj₁_inter]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨Y₂, hY₂mem, hY₂eq⟩ := mem_subset_inj₁ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
          obtain ⟨j, hj⟩ := P₁.surj hY₂mem
          refine Or.inr (Or.inr (Or.inr ⟨⟨hna, hnb⟩, j, ?_⟩))
          rw [hj]
          rw [hY₂eq] at hk
          exact inj₁_subset_inj₁.mp hk
        · rintro (⟨_, e2⟩ | ⟨_, e2⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨_, _⟩, j, hj⟩)
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · refine ⟨Nat.pair 1 j, ?_⟩
            rw [sumEnum_one (by rw [unpair_pair_fst]), unpair_pair_snd]
            exact inj₁_subset_inj₁.mpr hj
      ·
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        exact ⟨fun _ => Or.inr (Or.inl ⟨hnb0, hnb1⟩), fun _ => ⟨s.unpair.1, subset_rfl⟩⟩
    ·
      rw [sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]
      exact ⟨fun _ => Or.inl ⟨hna0, hna1⟩, fun _ => ⟨s.unpair.2, subset_rfl⟩⟩
  inter n m :=
    selectFn (1 - (2 - n.unpair.1)) m
      (selectFn (1 - (2 - m.unpair.1)) n
        (selectFn (1 - n.unpair.1)
          (Nat.pair 0 (P₀.inter n.unpair.2 m.unpair.2))
          (Nat.pair 1 (P₁.inter n.unpair.2 m.unpair.2))))
  inter_primrec := by
    have hnTag : Nat.Primrec (fun t => t.unpair.1.unpair.1) :=
      Nat.Primrec.left.comp Nat.Primrec.left
    have hmTag : Nat.Primrec (fun t => t.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp Nat.Primrec.right
    have hnIdx : Nat.Primrec (fun t => t.unpair.1.unpair.2) :=
      Nat.Primrec.right.comp Nat.Primrec.left
    have hmIdx : Nat.Primrec (fun t => t.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp Nat.Primrec.right
    have hP0 : Nat.Primrec (fun t => Nat.pair 0 (P₀.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2)) :=
      (Nat.Primrec.const 0).pair ((P₀.inter_primrec.comp (hnIdx.pair hmIdx)).of_eq fun t => by
        simp only [unpair_pair_fst, unpair_pair_snd])
    have hP1 : Nat.Primrec (fun t => Nat.pair 1 (P₁.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2)) :=
      (Nat.Primrec.const 1).pair ((P₁.inter_primrec.comp (hnIdx.pair hmIdx)).of_eq fun t => by
        simp only [unpair_pair_fst, unpair_pair_snd])
    have hcnMaster : Nat.Primrec (fun t => 1 - (2 - t.unpair.1.unpair.1)) :=
      primrec_sub₂ (Nat.Primrec.const 1) (primrec_sub₂ (Nat.Primrec.const 2) hnTag)
    have hcmMaster : Nat.Primrec (fun t => 1 - (2 - t.unpair.2.unpair.1)) :=
      primrec_sub₂ (Nat.Primrec.const 1) (primrec_sub₂ (Nat.Primrec.const 2) hmTag)
    have hcnZero : Nat.Primrec (fun t => 1 - t.unpair.1.unpair.1) :=
      primrec_sub₂ (Nat.Primrec.const 1) hnTag
    exact primrec_selectFn hcnMaster Nat.Primrec.right
      (primrec_selectFn hcmMaster Nat.Primrec.left
        (primrec_selectFn hcnZero hP0 hP1))
  inter_spec := by
    rintro n m ⟨k, hk⟩
    rcases tag_trichotomy n.unpair.1 with hna | hna | ⟨hna0, hna1⟩
    ·
      rw [show 1 - (2 - n.unpair.1) = 0 by omega, selectFn_zero]
      rcases tag_trichotomy m.unpair.1 with hmb | hmb | ⟨hmb0, hmb1⟩
      ·
        rw [show 1 - (2 - m.unpair.1) = 0 by omega, selectFn_zero,
          show 1 - n.unpair.1 = 1 by omega, selectFn_one,
          sumEnum_zero (by rw [unpair_pair_fst]), unpair_pair_snd,
          sumEnum_zero hna, sumEnum_zero hmb, inj₀_inter]
        rw [sumEnum_zero hna, sumEnum_zero hmb, inj₀_inter] at hk
        obtain ⟨X₂, hX₂mem, hX₂eq⟩ := mem_subset_inj₀ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
        obtain ⟨j, hj⟩ := P₀.surj hX₂mem
        rw [hX₂eq] at hk
        have hjsub : P₀.X j ⊆ P₀.X n.unpair.2 ∩ P₀.X m.unpair.2 := by
          rw [hj]; exact inj₀_subset_inj₀.mp hk
        rw [P₀.inter_spec ⟨j, hjsub⟩]
      ·
        exfalso
        rw [sumEnum_zero hna, sumEnum_one hmb, inj₀_inter_inj₁] at hk
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
        exact absurd (hk hx) (Set.notMem_empty x)
      ·
        rw [show 1 - (2 - m.unpair.1) = 1 by omega, selectFn_one,
          sumEnum_master hmb0 hmb1, sumEnum_inter_sumMaster]
    ·
      rw [show 1 - (2 - n.unpair.1) = 0 by omega, selectFn_zero]
      rcases tag_trichotomy m.unpair.1 with hmb | hmb | ⟨hmb0, hmb1⟩
      ·
        exfalso
        rw [sumEnum_one hna, sumEnum_zero hmb, Set.inter_comm, inj₀_inter_inj₁] at hk
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
        exact absurd (hk hx) (Set.notMem_empty x)
      ·
        rw [show 1 - (2 - m.unpair.1) = 0 by omega, selectFn_zero,
          show 1 - n.unpair.1 = 0 by omega, selectFn_zero,
          sumEnum_one (by rw [unpair_pair_fst]), unpair_pair_snd,
          sumEnum_one hna, sumEnum_one hmb, inj₁_inter]
        rw [sumEnum_one hna, sumEnum_one hmb, inj₁_inter] at hk
        obtain ⟨Y₂, hY₂mem, hY₂eq⟩ := mem_subset_inj₁ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
        obtain ⟨j, hj⟩ := P₁.surj hY₂mem
        rw [hY₂eq] at hk
        have hjsub : P₁.X j ⊆ P₁.X n.unpair.2 ∩ P₁.X m.unpair.2 := by
          rw [hj]; exact inj₁_subset_inj₁.mp hk
        rw [P₁.inter_spec ⟨j, hjsub⟩]
      ·
        rw [show 1 - (2 - m.unpair.1) = 1 by omega, selectFn_one,
          sumEnum_master hmb0 hmb1, sumEnum_inter_sumMaster]
    ·
      rw [show 1 - (2 - n.unpair.1) = 1 by omega, selectFn_one,
        sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]
  masterIdx := Nat.pair 2 0
  masterIdx_spec := by
    rw [sumEnum_master (by rw [unpair_pair_fst]; decide) (by rw [unpair_pair_fst]; decide)]
    rfl

theorem sum_isEffectivelyGiven (g₀ : V₀.IsEffectivelyGiven) (g₁ : V₁.IsEffectivelyGiven) :
    (sum V₀ V₁ h₀ h₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := g₀; obtain ⟨P₁⟩ := g₁
  exact ⟨sumPresentation P₀ P₁⟩

@[simp] theorem sumPresentation_X (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) : (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁)).X t = sumEnum P₀ P₁ t := rfl

theorem inMap₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap P₀ (sumPresentation P₀ P₁) (inMap₀ (h₀ := h₀) (h₁ := h₁)) := by
  constructor
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hmtag0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hmtag1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hincl0 : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hmtag0.and hincl0).or (hmtag0.not.and hmtag1.not))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨hm0, hm1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hm] at hsub
      exact Or.inl ⟨hm, inj₀_subset_inj₀.mp hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨P₀.mem_X _, sumEnum_mem _, ?_⟩
        rw [sumEnum_zero hm]; exact inj₀_subset_inj₀.mpr hsub
      · exfalso; omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hm] at hsub
      exact (not_inj₀_subset_inj₁ (h₀ _ (P₀.mem_X _)) hsub).elim
    · rintro (⟨e1, _⟩ | ⟨_, e2⟩) <;> exfalso <;> omega
  · constructor
    · intro _; exact Or.inr ⟨hm0, hm1⟩
    · intro _
      refine ⟨P₀.mem_X _, sumEnum_mem _, ?_⟩
      rw [sumEnum_master hm0 hm1]; exact inj₀_subset_sumMaster (P₀.mem_X _)

theorem inMap₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap P₁ (sumPresentation P₀ P₁) (inMap₁ (h₀ := h₀) (h₁ := h₁)) := by
  constructor
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hmtag0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hmtag1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hincl1 : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hmtag1.and hincl1).or (hmtag0.not.and hmtag1.not))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨hm0, hm1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hm] at hsub
      exact (not_inj₁_subset_inj₀ (h₁ _ (P₁.mem_X _)) hsub).elim
    · rintro (⟨e1, _⟩ | ⟨_, e2⟩) <;> exfalso <;> omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hm] at hsub
      exact Or.inl ⟨hm, inj₁_subset_inj₁.mp hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨P₁.mem_X _, sumEnum_mem _, ?_⟩
        rw [sumEnum_one hm]; exact inj₁_subset_inj₁.mpr hsub
      · exfalso; omega
  · constructor
    · intro _; exact Or.inr ⟨hm0, hm1⟩
    · intro _
      refine ⟨P₁.mem_X _, sumEnum_mem _, ?_⟩
      rw [sumEnum_master hm0 hm1]; exact inj₁_subset_sumMaster (P₁.mem_X _)

theorem outMap₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap (sumPresentation P₀ P₁) P₀ (outMap₀ (h₀ := h₀) (h₁ := h₁)) := by
  constructor
  obtain ⟨k0, hk0⟩ := P₀.surj V₀.master_mem
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hntag0 : RecDecidable (fun s => s.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hincl_left : RecDecidable (fun s => P₀.X s.unpair.1.unpair.2 ⊆ P₀.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hincl_master : RecDecidable (fun s => P₀.X k0 ⊆ P₀.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.const k0).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hntag0.and hincl_left).or (hntag0.not.and hincl_master))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨hn0, hn1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hn, leftPart_inj₀] at hsub
      exact Or.inl ⟨hn, hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨sumEnum_mem _, P₀.mem_X _, ?_⟩
        rw [sumEnum_zero hn, leftPart_inj₀]; exact hsub
      · exfalso; omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hn, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _))] at hsub
      refine Or.inr ⟨by omega, ?_⟩
      rw [hk0]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₀.mem_X _, ?_⟩
        rw [sumEnum_one hn, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _)), ← hk0]; exact hsub
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_master hn0 hn1, leftPart_sumMaster] at hsub
      refine Or.inr ⟨hn0, ?_⟩
      rw [hk0]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₀.mem_X _, ?_⟩
        rw [sumEnum_master hn0 hn1, leftPart_sumMaster, ← hk0]; exact hsub

theorem outMap₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap (sumPresentation P₀ P₁) P₁ (outMap₁ (h₀ := h₀) (h₁ := h₁)) := by
  constructor
  obtain ⟨k1, hk1⟩ := P₁.surj V₁.master_mem
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hntag1 : RecDecidable (fun s => s.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hincl_right : RecDecidable (fun s => P₁.X s.unpair.1.unpair.2 ⊆ P₁.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hincl_master : RecDecidable (fun s => P₁.X k1 ⊆ P₁.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.const k1).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hntag1.and hincl_right).or (hntag1.not.and hincl_master))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨hn0, hn1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hn, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _))] at hsub
      refine Or.inr ⟨by omega, ?_⟩
      rw [hk1]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₁.mem_X _, ?_⟩
        rw [sumEnum_zero hn, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _)), ← hk1]; exact hsub
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hn, rightPart_inj₁] at hsub
      exact Or.inl ⟨hn, hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨sumEnum_mem _, P₁.mem_X _, ?_⟩
        rw [sumEnum_one hn, rightPart_inj₁]; exact hsub
      · exfalso; omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_master hn0 hn1, rightPart_sumMaster] at hsub
      refine Or.inr ⟨hn1, ?_⟩
      rw [hk1]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₁.mem_X _, ?_⟩
        rw [sumEnum_master hn0 hn1, rightPart_sumMaster, ← hk1]; exact hsub

theorem sumMap_isComputable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
    (Q₀ : ComputablePresentation V₀') (Q₁ : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : ComputableMap P₀ Q₀ f) (hg : ComputableMap P₁ Q₁ g) :
    ComputableMap (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁))
      (sumPresentation Q₀ Q₁ (h₀ := h₀') (h₁ := h₁'))
      (sumMap f g) := by
  constructor
  have hf' : REPred (fun u => f.rel (P₀.X u.unpair.1) (Q₀.X u.unpair.2)) := hf.out
  have hg' : REPred (fun u => g.rel (P₁.X u.unpair.1) (Q₁.X u.unpair.2)) := hg.out
  have hNtag0 : RecDecidable (fun s => s.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hNtag1 : RecDecidable (fun s => s.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hMtag0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hMtag1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hfr : REPred (fun s => f.rel (P₀.X s.unpair.1.unpair.2) (Q₀.X s.unpair.2.unpair.2)) :=
    REPred.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf'.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hgr : REPred (fun s => g.rel (P₁.X s.unpair.1.unpair.2) (Q₁.X s.unpair.2.unpair.2)) :=
    REPred.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg'.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hA : REPred (fun s => s.unpair.2.unpair.1 ≠ 0 ∧ s.unpair.2.unpair.1 ≠ 1) :=
    (hMtag0.not.and hMtag1.not).re
  have hB : REPred (fun s => (s.unpair.1.unpair.1 = 0 ∧ s.unpair.2.unpair.1 = 0)
      ∧ f.rel (P₀.X s.unpair.1.unpair.2) (Q₀.X s.unpair.2.unpair.2)) :=
    ((hNtag0.and hMtag0).re).and hfr
  have hC : REPred (fun s => (s.unpair.1.unpair.1 = 1 ∧ s.unpair.2.unpair.1 = 1)
      ∧ g.rel (P₁.X s.unpair.1.unpair.2) (Q₁.X s.unpair.2.unpair.2)) :=
    ((hNtag1.and hMtag1).re).and hgr
  refine REPred.of_iff (fun s => ?_) (hA.or (hB.or hC))
  simp only [sumPresentation_X]
  constructor
  · rintro ⟨_, _, hdisj⟩
    rcases hdisj with hM | ⟨X, Y', hWX, hWY, hfXY⟩ | ⟨Y, Y', hWY, hWY', hgYY⟩
    · left
      rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | hm
      · rw [sumEnum_zero hm] at hM; exact absurd hM inj₀_ne_sumMaster
      · rw [sumEnum_one hm] at hM; exact absurd hM inj₁_ne_sumMaster
      · exact hm
    · right; left
      have ha : s.unpair.1.unpair.1 = 0 ∧ X = P₀.X s.unpair.1.unpair.2 := by
        rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨h0, h1⟩
        · rw [sumEnum_zero hn] at hWX; exact ⟨hn, (inj₀_eq_iff.mp hWX).symm⟩
        · rw [sumEnum_one hn] at hWX
          exact absurd hWX.symm (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
        · rw [sumEnum_master h0 h1] at hWX; exact absurd hWX.symm inj₀_ne_sumMaster
      have hb : s.unpair.2.unpair.1 = 0 ∧ Y' = Q₀.X s.unpair.2.unpair.2 := by
        rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨h0, h1⟩
        · rw [sumEnum_zero hm] at hWY; exact ⟨hm, (inj₀_eq_iff.mp hWY).symm⟩
        · rw [sumEnum_one hm] at hWY
          exact absurd hWY.symm (inj₀_ne_inj₁_of_nonempty (h₁' _ (Q₁.mem_X _)))
        · rw [sumEnum_master h0 h1] at hWY; exact absurd hWY.symm inj₀_ne_sumMaster
      obtain ⟨ha0, hX⟩ := ha; obtain ⟨hb0, hY⟩ := hb
      subst hX; subst hY
      exact ⟨⟨ha0, hb0⟩, hfXY⟩
    · right; right
      have ha : s.unpair.1.unpair.1 = 1 ∧ Y = P₁.X s.unpair.1.unpair.2 := by
        rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨h0, h1⟩
        · rw [sumEnum_zero hn] at hWY
          exact (inj₀_eq_inj₁_elim (h₀ _ (P₀.mem_X _)) hWY).elim
        · rw [sumEnum_one hn] at hWY; exact ⟨hn, (inj₁_eq_iff.mp hWY).symm⟩
        · rw [sumEnum_master h0 h1] at hWY; exact absurd hWY.symm inj₁_ne_sumMaster
      have hb : s.unpair.2.unpair.1 = 1 ∧ Y' = Q₁.X s.unpair.2.unpair.2 := by
        rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨h0, h1⟩
        · rw [sumEnum_zero hm] at hWY'
          exact (inj₀_eq_inj₁_elim (h₀' _ (Q₀.mem_X _)) hWY').elim
        · rw [sumEnum_one hm] at hWY'; exact ⟨hm, (inj₁_eq_iff.mp hWY').symm⟩
        · rw [sumEnum_master h0 h1] at hWY'; exact absurd hWY'.symm inj₁_ne_sumMaster
      obtain ⟨ha1, hYeq⟩ := ha; obtain ⟨hb1, hY'eq⟩ := hb
      subst hYeq; subst hY'eq
      exact ⟨⟨ha1, hb1⟩, hgYY⟩
  · rintro (⟨hm0, hm1⟩ | ⟨⟨hn0, hm0⟩, hfXY⟩ | ⟨⟨hn1, hm1⟩, hgYY⟩)
    · exact ⟨sumEnum_mem _, sumEnum_mem _, Or.inl (sumEnum_master hm0 hm1)⟩
    · exact ⟨sumEnum_mem _, sumEnum_mem _,
        Or.inr (Or.inl ⟨_, _, sumEnum_zero hn0, sumEnum_zero hm0, hfXY⟩)⟩
    · exact ⟨sumEnum_mem _, sumEnum_mem _,
        Or.inr (Or.inr ⟨_, _, sumEnum_one hn1, sumEnum_one hm1, hgYY⟩)⟩

end Sum

end

end DomainTheory.NeighbourhoodSystems
