module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mapM_natBool_isSome_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- **7.22i(b)1(d):** list decode succeeds iff every coded entry is a binary digit. -/
theorem decodeListBool_isSome_iff (n : ℕ) :
    (decodeListBool n).isSome = true ↔ allBinDigitsChar n = 1 := by
  simp only [decodeListBool, mapM_natBool_isSome_iff, allBinDigitsChar_eq_one_iff]

end Exercise722

end DomainTheory.NeighbourhoodSystems
