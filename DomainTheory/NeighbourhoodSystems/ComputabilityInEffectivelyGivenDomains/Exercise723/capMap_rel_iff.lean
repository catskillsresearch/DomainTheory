/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
