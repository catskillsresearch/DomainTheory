/-ai
The sum presentation enumerates by tags: tag zero is a left copy of a neighbourhood of the first system, tag one is a right copy of a neighbourhood of the second, and any other tag is the sum master. Every enumerated set is a sum neighbourhood, and every sum neighbourhood arises, the master at tag two and the copies at tags zero and one from indices of the factors. Intersection-equality and consistency are recursively decidable by combining equality of enumerated neighbourhoods, the tag tests, and the factors' intersection and consistency deciders. The tag trichotomy checks the equivalences: a master factor is absorbed, two copies of the same side reduce to the corresponding factor, and opposite sides meet emptily, which cannot equal a nonempty enumerated neighbourhood or contain one. The intersection code is the primitive-recursive selection that returns the other code when one tag is a master and otherwise pairs tag zero or one with the factor intersection. Its specification follows the same split, using the factor specifications on matching copies and refuting opposite sides by nonemptiness. The master code is the pair of two and zero, which enumerates the sum master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.tag_trichotomy
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₁_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_ne_sumMaster
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₁_ne_sumMaster
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_ne_inj₁_of_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.eqSEdec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_eq_inj₁_elim
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumMaster_inter_sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_inter_sumMaster

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

include h₀ h₁

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `𝒟₀ + 𝒟₁` is effectively given.** The tag enumeration
`Z (pair 0 n) = 0X⁰ₙ`, `Z (pair 1 n) = 1X¹ₙ`, `Z (pair (≥2) _) = M`. Scott's 7.1(i)/(ii) follow the
intersection table: master absorbs, `0X ∩ 0X' = 0(X∩X')` reduces to `𝒟₀`, `0X ∩ 1Y = ∅` is
impossible (non-emptiness). The deciders are assembled from `eqSEdec`, the tag deciders
(`natEq`/`not`/`and`/`or`), and the components' `interEq`/`cons`. -/
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
      · -- na = 0, nb = 0
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
      · -- na = 0, nb = 1: ∅
        rw [sumEnum_zero hna, sumEnum_one hnb, inj₀_inter_inj₁]
        constructor
        · intro h
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) t.unpair.2.unpair.2
          rw [← h] at hx
          exact absurd hx (Set.notMem_empty x)
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
      · -- na = 0, nb = M: master on the right
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        constructor
        · intro h; exact Or.inr (Or.inl ⟨⟨hnb0, hnb1⟩, h⟩)
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨_, h⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
          · exfalso; omega
          · exact h
          · exfalso; omega
          · exfalso; omega
    · rcases tag_trichotomy t.unpair.2.unpair.1.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
      · -- na = 1, nb = 0: ∅
        rw [sumEnum_one hna, sumEnum_zero hnb, Set.inter_comm, inj₀_inter_inj₁]
        constructor
        · intro h
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) t.unpair.2.unpair.2
          rw [← h] at hx
          exact absurd hx (Set.notMem_empty x)
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩) <;> exfalso <;> omega
      · -- na = 1, nb = 1
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
      · -- na = 1, nb = M
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        constructor
        · intro h; exact Or.inr (Or.inl ⟨⟨hnb0, hnb1⟩, h⟩)
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨_, h⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩)
          · exfalso; omega
          · exact h
          · exfalso; omega
          · exfalso; omega
    · -- na = M: master on the left (any nb)
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
      · -- na = 0, nb = 0
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
      · -- na = 0, nb = 1: ∅
        rw [sumEnum_zero hna, sumEnum_one hnb, inj₀_inter_inj₁]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
          exact absurd (hk hx) (Set.notMem_empty x)
        · rintro (⟨e1, _⟩ | ⟨_, e2⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨e1, _⟩, _⟩) <;> exfalso <;> omega
      · -- na = 0, nb = M: right master
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        exact ⟨fun _ => Or.inr (Or.inl ⟨hnb0, hnb1⟩), fun _ => ⟨s.unpair.1, subset_rfl⟩⟩
    · rcases tag_trichotomy s.unpair.2.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
      · -- na = 1, nb = 0: ∅
        rw [sumEnum_one hna, sumEnum_zero hnb, Set.inter_comm, inj₀_inter_inj₁]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
          exact absurd (hk hx) (Set.notMem_empty x)
        · rintro (⟨_, e2⟩ | ⟨e1, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨_, e2⟩, _⟩) <;> exfalso <;> omega
      · -- na = 1, nb = 1
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
      · -- na = 1, nb = M: right master
        rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
        exact ⟨fun _ => Or.inr (Or.inl ⟨hnb0, hnb1⟩), fun _ => ⟨s.unpair.1, subset_rfl⟩⟩
    · -- na = M: left master (any nb)
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
    · -- n is a left copy (tag 0)
      rw [show 1 - (2 - n.unpair.1) = 0 by omega, selectFn_zero]
      rcases tag_trichotomy m.unpair.1 with hmb | hmb | ⟨hmb0, hmb1⟩
      · -- m left copy: consistent left ∩ left
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
      · -- m right copy: inconsistent (∅), refute consistency
        exfalso
        rw [sumEnum_zero hna, sumEnum_one hmb, inj₀_inter_inj₁] at hk
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
        exact absurd (hk hx) (Set.notMem_empty x)
      · -- m master
        rw [show 1 - (2 - m.unpair.1) = 1 by omega, selectFn_one,
          sumEnum_master hmb0 hmb1, sumEnum_inter_sumMaster]
    · -- n is a right copy (tag 1)
      rw [show 1 - (2 - n.unpair.1) = 0 by omega, selectFn_zero]
      rcases tag_trichotomy m.unpair.1 with hmb | hmb | ⟨hmb0, hmb1⟩
      · -- m left copy: inconsistent
        exfalso
        rw [sumEnum_one hna, sumEnum_zero hmb, Set.inter_comm, inj₀_inter_inj₁] at hk
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
        exact absurd (hk hx) (Set.notMem_empty x)
      · -- m right copy: consistent right ∩ right
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
      · -- m master
        rw [show 1 - (2 - m.unpair.1) = 1 by omega, selectFn_one,
          sumEnum_master hmb0 hmb1, sumEnum_inter_sumMaster]
    · -- n master
      rw [show 1 - (2 - n.unpair.1) = 1 by omega, selectFn_one,
        sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]
  masterIdx := Nat.pair 2 0
  masterIdx_spec := by
    rw [sumEnum_master (by rw [unpair_pair_fst]; decide) (by rw [unpair_pair_fst]; decide)]
    rfl

end Sum

end DomainTheory.NeighbourhoodSystems
