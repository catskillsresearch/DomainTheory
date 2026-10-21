/-ai
The approximable map cupMap from the product of PN with itself to PN interprets binary union. A product neighbourhood of X and Y is related to Z when X, Y, and Z are neighbourhoods of PN and the intersection of X and Y is contained in Z, which is the neighbourhood form of demanding that the excluded set of Z fit inside the union of the excluded sets. Domain and codomain membership are the product of the inputs and the output neighbourhood. The master input uses that the intersection of the whole set with itself is contained in the master output. The intersection of two related outputs is again the neighbourhood of a bitwise disjunction of indices. Monotonicity shrinks both input factors and composes the resulting intersection inclusion with the original inclusion and the output inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **`λx,y. x∪y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to
`Z` iff `nbhd(myLor n m) ⊆ Z` — the excluded set of `Z` must fit inside the *union* `Eₙ ∪ Eₘ`, i.e.
`nbhd n ∩ nbhd m ⊆ Z` (`Eₙ ∪ Eₘ = E_{myLor n m}`, `nbhd_inter`). -/
def cupMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    Set.inter_subset_left.trans (Set.subset_univ _)⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXYZ⟩ ⟨X', Y', heq, _, _, hZ', hXYZ'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    exact ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, Set.subset_inter hXYZ hXYZ'⟩
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXYZ⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    exact ⟨X', Y', rfl, hX', hY', hZ',
      (Set.inter_subset_inter hXX' hYY').trans (hXYZ.trans hZZ')⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
