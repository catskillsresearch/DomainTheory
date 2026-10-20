module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_cons_iff_nonempty_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(ii) for `𝒰`**: consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable, via
`U_cons_iff_nonempty_inter` and `recDecidable_presentedIntervals_nonempty`. -/
theorem U_cons_computable : RecDecidable₂ (fun n m => ∃ k, UX k ⊆ UX n ∩ UX m) := by
  unfold RecDecidable₂
  have hcomb : Nat.Primrec (fun t : ℕ => combineCode (canonCode t.unpair.1) (canonCode t.unpair.2)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
      (primrec_canonCode.comp Nat.Primrec.right))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable_presentedIntervals_nonempty.comp hcomb)
  show (∃ k, UX k ⊆ UX t.unpair.1 ∩ UX t.unpair.2) ↔ _
  rw [U_cons_iff_nonempty_inter, UX, UX, presentedIntervals_decodeQPairList_combineCode]

end DomainTheory.NeighbourhoodSystems
