module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **`λx,y. x∩y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to
`Z` iff `X ⊆ Z` and `Y ⊆ Z` (the "test at the minimal witness" idiom: `X`, `Y` are themselves the
tightest possible arguments consistent with the input information). -/
def capMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ X ⊆ Z ∧ Y ⊆ Z
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    Set.subset_univ _, Set.subset_univ _⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXZ, hYZ⟩ ⟨X', Y', heq, _, _, hZ', hXZ', hYZ'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    exact ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩,
      Set.subset_inter hXZ hXZ', Set.subset_inter hYZ hYZ'⟩
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXZ, hYZ⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    exact ⟨X', Y', rfl, hX', hY', hZ', hXX'.trans (hXZ.trans hZZ'), hYY'.trans (hYZ.trans hZZ')⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
