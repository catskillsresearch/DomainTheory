module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.gLastOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.gStepsOK
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.codePair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.chainDec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixPStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixChainChar

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


/-- The `foldCode` flag is `1` iff the start flag is `1` and the whole chain is consistent. -/
theorem fixPStep_foldl_snd (fincl : ℕ → ℕ) (c : ℕ) :
    ∀ (full : List ℕ) (prev fl : ℕ), fl ≤ 1 →
      ((List.foldl (fixPStep fincl c) (Nat.pair prev fl) full).unpair.2 = 1 ↔
        fl = 1 ∧ chainDec fincl c prev full) := by
  intro full
  induction full with
  | nil =>
    intro prev fl _
    show (Nat.pair prev fl).unpair.2 = 1 ↔ fl = 1 ∧ chainDec fincl c prev []
    rw [unpair_pair_snd]
    simp [chainDec]
  | cons b rest ih =>
    intro prev fl _
    rw [List.foldl_cons]
    have hstep : fixPStep fincl c (Nat.pair prev fl) b
        = Nat.pair b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0) := by
      unfold fixPStep; simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hstep]
    set nf := selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0 with hnf
    have hnfle : nf ≤ 1 := by
      rw [hnf]
      rcases (show fl = 0 ∨ fl = 1 by omega) with h | h <;> rw [h]
      · rw [selectFn_zero]; exact Nat.zero_le 1
      · rw [selectFn_one]; exact isOne_le_one _
    rw [ih b nf hnfle]
    have hnf1 : nf = 1 ↔ (fl = 1 ∧ fincl (Nat.pair c (codePair prev b)) = 1) := by
      rw [hnf]
      rcases (show fl = 0 ∨ fl = 1 by omega) with h | h <;> rw [h]
      · rw [selectFn_zero]; simp
      · rw [selectFn_one, isOne_eq_one_iff]; simp
    rw [hnf1]
    constructor
    · rintro ⟨⟨hfl1, hfincl1⟩, hrest⟩; exact ⟨hfl1, hfincl1, hrest⟩
    · rintro ⟨hfl1, hfincl1, hrest⟩; exact ⟨⟨hfl1, hfincl1⟩, hrest⟩

end DomainTheory.NeighbourhoodSystems
