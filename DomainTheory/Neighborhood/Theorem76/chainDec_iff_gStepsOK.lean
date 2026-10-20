/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Theorem76.Basic
import DomainTheory.Neighborhood.Theorem76.Xenum_codePair
import DomainTheory.Neighborhood.Theorem76.leastMap_Xenum_rel


namespace DomainTheory.Neighborhood

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

end DomainTheory.Neighborhood
