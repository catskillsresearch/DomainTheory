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






















































theorem nextCellStep_eq (n m : ℕ) :
    nextCellStep (Nat.pair n m) = Nat.pair (nextCell (n, m)).1 (nextCell (n, m)).2 := by
  unfold nextCellStep
  simp only [unpair_pair_fst, unpair_pair_snd]
  rcases n with _ | k
  · have hz : isZero 0 = 1 := by unfold isZero; omega
    rw [hz, selectFn_one]; rfl
  · have hz : isZero (k + 1) = 0 := by unfold isZero; omega
    rw [hz, selectFn_zero]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
