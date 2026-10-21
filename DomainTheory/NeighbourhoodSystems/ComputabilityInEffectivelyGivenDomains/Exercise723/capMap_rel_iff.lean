/-ai
On neighbourhood indices, capMap relates the product of nbhd n and nbhd m to nbhd k if and only if both nbhd n and nbhd m are contained in nbhd k.

From a related triple, injectivity of product neighbourhoods recovers the two factors, and the relation supplies the two inclusions. Conversely, the three neighbourhoods themselves are the required witnesses.
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


/-- `capMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff both
`nbhd n ⊆ nbhd k` and `nbhd m ⊆ nbhd k`. -/
theorem capMap_rel_iff (n m k : ℕ) :
    capMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd n ⊆ nbhd k ∧ nbhd m ⊆ nbhd k := by
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXZ, hYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hXZ, hYZ⟩
  · rintro ⟨hXZ, hYZ⟩
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, hXZ, hYZ⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
