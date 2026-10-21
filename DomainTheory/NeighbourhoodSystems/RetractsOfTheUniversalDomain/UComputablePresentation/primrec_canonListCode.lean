/-ai
The canonical list code is primitive recursive.

The filter step of the right projection is primitive recursive. The flat map of that function, fed the pair of the constant zero and the input, equals the canonical list code once the pair is unpacked.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_canonListCode : Nat.Primrec canonListCode := by
  have hg : Nat.Primrec (fun t : ℕ => canonFilterStep t.unpair.2) :=
    primrec_canonFilterStep.comp Nat.Primrec.right
  exact ((primrec_flatMapCode hg).comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq
    fun c => by
      unfold canonListCode
      simp only [id, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
