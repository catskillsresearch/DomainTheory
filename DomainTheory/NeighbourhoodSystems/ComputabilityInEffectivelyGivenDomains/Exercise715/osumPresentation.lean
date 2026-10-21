/-ai
A Scott presentation of the coalesced sum enumerates neighbourhoods by the coalesced-sum enumeration. The master is a code of tag 2. A proper left neighbourhood is tag 0 on an index of that neighbourhood, and a proper right neighbourhood is tag 1 on an index of that neighbourhood. Intersection-equality reduces to the separated-sum presentation along a primitive-recursive normalization, built from the properness deciders, that sends a proper left code to tag 0 on its index, a proper right code to tag 1 on its index, and every other code to a fixed master code. Consistency is the disjunction of either code enumerating the master, in which case the other code is a witness, with both codes being proper on the same side and consistent in that component, in which case a component witness that stays proper is retagged to that side; codes on opposite sides have empty intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.proper₀_dec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.proper₁_dec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_left
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_right
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_subset_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

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

end DomainTheory.NeighbourhoodSystems
