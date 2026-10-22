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


/-- **The reversal fact.** `nbhd n ⊆ nbhd k ↔ myLor n k = n`: `nbhd n ⊆ nbhd k` iff
`nbhd n ∩ nbhd k = nbhd n` iff (by `nbhd_inter` + injectivity) `nbhd (myLor n k) = nbhd n`. -/
theorem nbhd_subset_iff_myLor_eq (n k : ℕ) : nbhd n ⊆ nbhd k ↔ myLor n k = n := by
  constructor
  · intro h
    apply nbhd_injective
    rw [← nbhd_inter]
    exact (Set.inter_eq_left.mpr h)
  · intro h
    rw [← h, ← nbhd_inter]
    exact Set.inter_subset_right

end DomainTheory.NeighbourhoodSystems.Exercise723
