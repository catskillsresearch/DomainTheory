/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices


























theorem sigmaJ_pair_union (j j' m : ℕ) (hne : j ≠ j') :
    sigmaJ j (({pair j m} : Pomega) ∪ {pair j' m}) =
      ({pair j (m + 1)} : Pomega) := by
  ext p
  constructor
  · intro ⟨k, hp, hk⟩
    rcases hk with hk | hk
    · have hkm : k = m := (pair_inj hk).2
      subst k
      simpa using hp.symm
    · have hj : j = j' := (pair_inj hk).1
      exact (hne hj).elim
  · intro hp
    exact ⟨m, hp.symm, Or.inl (by simp)⟩

end DomainTheory.DataTypesAsLattices
