module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i) for `𝒰`**: `Xₙ ∩ Xₘ = X_k` is recursively decidable. Reduces to
`recDecidable₂_presentedIntervals_eq` on the codes `combineCode (canonCode n) (canonCode m)`
(realizing `Xₙ ∩ Xₘ`) and `canonCode k` (realizing `X_k`). -/
theorem U_interEq_computable : RecDecidable₃ (fun n m k => UX n ∩ UX m = UX k) := by
  unfold RecDecidable₃
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h3 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcomb : Nat.Primrec (fun t : ℕ =>
      combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp h1).pair (primrec_canonCode.comp h2))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hg : Nat.Primrec (fun t : ℕ =>
      Nat.pair (combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1))
        (canonCode t.unpair.2.unpair.2)) := hcomb.pair (primrec_canonCode.comp h3)
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable₂_presentedIntervals_eq.comp hg)
  show UX t.unpair.1 ∩ UX t.unpair.2.unpair.1 = UX t.unpair.2.unpair.2 ↔ _
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [UX, UX, UX, presentedIntervals_decodeQPairList_combineCode]

end DomainTheory.NeighbourhoodSystems
