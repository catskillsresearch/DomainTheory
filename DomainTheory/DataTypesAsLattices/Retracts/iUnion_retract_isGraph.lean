/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.retract_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem iUnion_retract_isGraph {xs : ℕ → Pomega} (h : ∀ n, IsRetract (xs n)) :
    IsGraph (⋃ n, xs n) := by
  intro k m n hkm hkn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hkm
  have hiG : IsGraph (xs i) := (theorem_1_2_iii (xs i)).mp (retract_isGraph (h i))
  exact Set.mem_iUnion.mpr ⟨i, hiG hi hkn⟩

end DomainTheory.DataTypesAsLattices
