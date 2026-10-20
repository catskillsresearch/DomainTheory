/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise813a.Basic
import DomainTheory.Neighborhood.Exercise813a.affine_eq_biInter


namespace DomainTheory.Neighborhood

open NeighborhoodSystem











theorem generatedBy_affine (k ℓ : ℕ) (hℓ : ℓ < 2 ^ k) : GeneratedBy generator (affine k ℓ) := by
  rw [affine_eq_biInter k ℓ hℓ]
  induction Finset.range k using Finset.induction_on with
  | empty => simpa using GeneratedBy.univ
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    refine GeneratedBy.inter ?_ ih
    split_ifs with hb
    · exact GeneratedBy.of _
    · exact GeneratedBy.compl (GeneratedBy.of _)

end DomainTheory.Neighborhood
