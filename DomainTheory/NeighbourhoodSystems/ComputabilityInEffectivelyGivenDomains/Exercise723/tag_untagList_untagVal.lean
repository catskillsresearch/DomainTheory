/-ai
The list code and the value extracted from a code decode that code under tag. Tag of the decoded list of the extracted list code, at the extracted value, returns the original code.

Rewrite by the decoding equation for the extracted list and the specification of the extracted value, then apply the right-inverse theorem for the reference decoder.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tag_untagRef
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.decodeList_untagList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagVal_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

































































/-- **`untagList`/`untagVal` genuinely decode `tag`.** -/
theorem tag_untagList_untagVal (c : ℕ) : tag (decodeList (untagList c)) (untagVal c) = c := by
  rw [decodeList_untagList, untagVal_spec]; exact tag_untagRef c

end DomainTheory.NeighbourhoodSystems.Exercise723
