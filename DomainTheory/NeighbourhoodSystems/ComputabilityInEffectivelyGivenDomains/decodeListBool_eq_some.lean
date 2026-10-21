/-ai
If decoding a natural number as a list of booleans yields a list, then the number is the boolean-list code of that list.

The hypothesis means that the underlying list decode is the list mapped by the boolean-to-natural encoding. The number equals the list code of its list decode, which equals the list code of that image, which is the boolean-list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mapM_natBool_eq_some

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem decodeListBool_eq_some (n : ℕ) (σ : List Bool) (h : decodeListBool n = some σ) :
    n = encodeListBool σ := by
  have hl : decodeList n = σ.map boolNat := mapM_natBool_eq_some (decodeList n) σ h
  calc n = encodeList (decodeList n) := (encodeList_decodeList n).symm
    _ = encodeList (σ.map boolNat) := by rw [hl]
    _ = encodeListBool σ := rfl

end Exercise722

end DomainTheory.NeighbourhoodSystems
