/-ai
Decoding a list code is injective: equal decoded lists come from equal codes. The decoder has a left inverse, namely encodeList.

Apply encodeList to the equality of decoded lists and rewrite both sides by the round trip encodeList_decodeList.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)










































































/-- **`decodeList` is injective**, immediately from the round-trip `encodeList_decodeList`
(`decodeList` has a left inverse). -/
theorem decodeList_injective {a b : ℕ} (h : decodeList a = decodeList b) : a = b := by
  have := congrArg encodeList h
  rwa [encodeList_decodeList, encodeList_decodeList] at this

end DomainTheory.NeighbourhoodSystems.Exercise723
