/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise122
import DomainTheory.Neighborhood.Exercise213.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem



theorem principalFamily_directed (x : V₀.Element) :
    ∀ i j : {X : Set α // x.mem X}, ∃ k : {X : Set α // x.mem X},
      V₀.principal (x.sub i.2) ≤ V₀.principal (x.sub k.2) ∧
        V₀.principal (x.sub j.2) ≤ V₀.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V₀.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V₀.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
