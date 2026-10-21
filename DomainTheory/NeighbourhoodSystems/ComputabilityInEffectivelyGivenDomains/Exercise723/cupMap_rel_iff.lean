/-ai
On neighbourhood indices, cupMap relates the product of nbhd n and nbhd m to nbhd k if and only if the neighbourhood of myLor n m is contained in nbhd k.

Rewrite the claimed inclusion by the intersection law for neighbourhoods. From a related triple, injectivity of product neighbourhoods recovers the factors, and the relation is the intersection inclusion. Conversely, the three neighbourhoods themselves witness the relation.
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


/-- `cupMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (myLor n m) ⊆ nbhd k`. -/
theorem cupMap_rel_iff (n m k : ℕ) :
    cupMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (myLor n m) ⊆ nbhd k := by
  rw [← nbhd_inter n m]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hXYZ
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
