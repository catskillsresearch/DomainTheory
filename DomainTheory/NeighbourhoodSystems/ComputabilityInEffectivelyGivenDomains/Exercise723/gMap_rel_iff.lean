/-ai
On neighbourhood indices, gMap relates the product of nbhd n and nbhd m to nbhd k if and only if the complement of nbhd k is contained in Fun of the complements of nbhd n and nbhd m.

From a related triple, injectivity of product neighbourhoods recovers the factors, and the relation is the Fun inclusion. Conversely, the three neighbourhoods themselves witness the relation.
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


/-- `gMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd k`'s excluded set fits inside `Fun (nbhd n)ᶜ (nbhd m)ᶜ`. -/
theorem gMap_rel_iff (n m k : ℕ) :
    gMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ (nbhd k)ᶜ ⊆ Fun (nbhd n)ᶜ (nbhd m)ᶜ := by
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
