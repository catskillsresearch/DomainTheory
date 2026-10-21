/-ai
A Scott presentation of the smash product enumerates neighbourhoods by the smash enumeration. The master is the code of the two master indices, and a proper product is the code of indices of its two factors. Intersection-equality rewrites each of the three codes, by properness deciders and selection, as a product of effective indices, and is then the conjunction of the two component intersection-equality predicates on those indices. Consistency holds when either code is improper, taking the other code as witness because an improper enumeration is the master and every enumerated set lies under the master, or when both codes are proper and both components are consistent, in which case indices of the two component intersections form a code of a neighbourhood contained in the intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_proper
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_subset_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_eq_prodNbhd_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_eq_eff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.proper₀_dec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.proper₁_dec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

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

end DomainTheory.NeighbourhoodSystems
