module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem Uinter_primrec : Nat.Primrec (fun t : ℕ => Uinter t.unpair.1 t.unpair.2) := by
  unfold Uinter
  exact (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
