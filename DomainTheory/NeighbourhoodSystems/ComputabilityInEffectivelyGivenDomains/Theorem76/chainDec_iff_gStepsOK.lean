/-ai
The decidable chain predicate holds of a list if and only if the least map of the enumerated neighbourhood of the function-space code takes consecutive steps along that list.

Induct on the list. The empty list holds on both sides. On a cons, the inclusion characteristic accepts the one-entry code if and only if the enumerated neighbourhood is contained in the corresponding step neighbourhood, and the least-map relation turns that inclusion into the least-map step. The inductive hypothesis handles the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Xenum_codePair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.leastMap_Xenum_rel

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


/-- `chainDec` is equivalent to `gStepsOK` of the least map, via the inclusion char's spec and
`Xenum (codePair a b) = [X_a, X_b]`. -/
theorem chainDec_iff_gStepsOK (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (fincl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2) (c : ℕ) :
    ∀ (full : List ℕ) (a : ℕ),
      chainDec fincl c a full ↔
        gStepsOK (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))) P a full := by
  intro full
  induction full with
  | nil => intro a; exact Iff.rfl
  | cons b rest ih =>
    intro a
    constructor
    · rintro ⟨hstep, hrest⟩
      refine ⟨?_, (ih b).mp hrest⟩
      rw [hfincl, unpair_pair_fst, unpair_pair_snd, Xenum_codePair P gN hgN a b] at hstep
      exact (leastMap_Xenum_rel P gN hgN c a b).mpr hstep
    · rintro ⟨hstep, hrest⟩
      refine ⟨?_, (ih b).mpr hrest⟩
      have hsub : Xenum P P gN c ⊆ step (P.X a) (P.X b) :=
        (leastMap_Xenum_rel P gN hgN c a b).mp hstep
      rw [hfincl, unpair_pair_fst, unpair_pair_snd, Xenum_codePair P gN hgN a b]
      exact hsub

end DomainTheory.NeighbourhoodSystems
