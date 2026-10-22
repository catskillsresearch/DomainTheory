module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodNbhd_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.tag_trichotomy
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.recDec_setEq₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.recDec_setEq₁
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.eqSEdec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_eq_inj₁_elim
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_subset_sumMaster
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumMaster_inter_sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_inter_sumMaster

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}


include h₀ h₁


/-- **Theorem 7.4 (Scott 1981, PRG-19).** The sum of effectively given domains is effectively given. -/
theorem sum_isEffectivelyGiven (g₀ : V₀.IsEffectivelyGiven) (g₁ : V₁.IsEffectivelyGiven) :
    (sum V₀ V₁ h₀ h₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := g₀; obtain ⟨P₁⟩ := g₁
  exact ⟨sumPresentation P₀ P₁⟩

@[simp] theorem sumPresentation_X (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) : (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁)).X t = sumEnum P₀ P₁ t := rfl

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `in₀` is computable.** `X⁰ₙ (in₀) Z_m ↔ 0X⁰ₙ ⊆ Z_m`, which
tag-decodes to `(m = 0X⁰ ∧ X⁰ₙ ⊆ X⁰_{m.2}) ∨ (m = master)` (`m = 1X¹` is impossible as `X⁰ₙ ≠ ∅`). -/
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

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `in₁` is computable.** Symmetric to `in₀`. -/
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

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `out₀` is computable.** `Z_n (out₀) X⁰_m ↔ leftPart Z_n ⊆
X⁰_m`; tag-decoded, `leftPart` is `X⁰_{n.2}` on a left copy and `Δ₀` on a right copy/master, so the
relation is `incl` against either `n.2` or the master index `k₀` (`X⁰_{k₀} = Δ₀`). -/
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

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `out₁` is computable.** Symmetric to `out₀` via `rightPart`. -/
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

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `f + g` is computable.** Tag-decoding the sum relation,
`Zₙ (f+g) W_m` holds iff `W_m` is the codomain master (decidable in `m`'s tag), or both are left
copies (tag `0`) with `X⁰_{n.2} f Y⁰_{m.2}`, or both are right copies (tag `1`) with
`X¹_{n.2} g Y¹_{m.2}`. The three disjuncts are r.e. (`REPred.or`): each copy case conjoins a decidable
tag test with the reindexed r.e. relation of `f`/`g`. -/
theorem sumMap_isComputable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
    (Q₀ : ComputablePresentation V₀') (Q₁ : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : ComputableMap P₀ Q₀ f) (hg : ComputableMap P₁ Q₁ g) :
    ComputableMap (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁))
      (sumPresentation Q₀ Q₁ (h₀ := h₀') (h₁ := h₁'))
      (sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g) := by
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
end DomainTheory.NeighbourhoodSystems
