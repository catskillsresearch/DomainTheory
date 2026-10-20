module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_nbhd_plusIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.nbhd_subset_iff_compl_subset_compl

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



























/-- `plusMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (plusIdx n m) ⊆ nbhd k`. -/
theorem plusMap_rel_iff (n m k : ℕ) :
    plusMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (plusIdx n m) ⊆ nbhd k := by
  rw [nbhd_subset_iff_compl_subset_compl, compl_nbhd_plusIdx]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
