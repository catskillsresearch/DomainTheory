/-ai
If the level set of a code is nonempty, canonicalization leaves the code unchanged.

Unfolding canonicalization, the nonemptiness test equals one, and selection on one
returns the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem canonIdx_eq_self_of_nonempty {c : ℕ} (h : (levelSet c.unpair.1 c.unpair.2).Nonempty) :
    canonIdx c = c := by
  unfold canonIdx
  rw [(myLevelSetNonempty_eq_one_iff _ _).mpr h, selectFn_one]

end DomainTheory.NeighbourhoodSystems
