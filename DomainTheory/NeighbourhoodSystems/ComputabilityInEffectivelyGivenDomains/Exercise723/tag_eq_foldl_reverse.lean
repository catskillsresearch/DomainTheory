/-ai
Tag of a list at a value equals the left fold, over the reversed list, of the map sending an accumulator and an entry to the numeral of the successor of the entry and the accumulator, starting from the numeral of zero and the value.

Rewrite by the identity that turns a left fold of a reversed list into a right fold, and apply the right-fold equation for tag.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tag_eq_foldr

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


theorem tag_eq_foldl_reverse (ns : List ℕ) (m : ℕ) :
    tag ns m = ns.reverse.foldl (fun acc a => num (a + 1) acc) (num 0 m) := by
  rw [List.foldl_reverse]; exact tag_eq_foldr ns m

end DomainTheory.NeighbourhoodSystems.Exercise723
