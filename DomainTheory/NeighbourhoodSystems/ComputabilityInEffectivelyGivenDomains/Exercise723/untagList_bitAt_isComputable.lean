/-ai
The list check that every index of the decoded extracted list has bit characteristic one is recursively decidable. The word is packed as the code followed by a dummy index and the bit word, the dummy riding along to match a later packing.

Transport the list-bounded universal quantification of the swapped bit-characteristic decider along the primitive-recursive extracted list of the first component, paired with the second component of the second component. The transport is the simplification of the unpairings.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_untagList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitAt_swap_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **The innermost list-check is recursively decidable.** Reindexes `bForallList` along
`untagList` to get `∀i ∈ decodeList (untagList c), bitAt m i = 1` as a function of `(c,m)`, packed
`(c,(j,m))`-style (`j` is a dummy free parameter here, along for the ride to match `gMap`'s later
packing). -/
theorem untagList_bitAt_isComputable :
    RecDecidable (fun w : ℕ => ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2 i = 1) :=
  RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
    (bitAt_swap_isComputable.bForallList.comp
      ((primrec_untagList.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))

end DomainTheory.NeighbourhoodSystems.Exercise723
