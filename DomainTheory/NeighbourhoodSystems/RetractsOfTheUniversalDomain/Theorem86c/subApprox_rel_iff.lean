/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem86
public import DomainTheory.Neighborhood.Theorem76
public import DomainTheory.Neighborhood.Theorem86c.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


/-- **`subApprox`'s relation, unfolded via `ofMono`/`ofContinuous`/`toFilter`.** `F subApprox G`
holds iff `G` is a genuine function-space neighbourhood containing `sub` of `F`'s least map (any
witnessing proof `hF` of `F`'s membership works, by proof irrelevance). -/
theorem subApprox_rel_iff {F G : Set (ApproximableMap E E)} (hF : (funSpace E E).mem F) :
    (subApprox (E := E)).rel F G ↔
      (funSpace E E).mem G ∧ sub (toApproxMap ((funSpace E E).principal hF)) ∈ G :=
  ⟨fun ⟨_, hG, hmem⟩ => ⟨hG, hmem⟩, fun ⟨hG, hmem⟩ => ⟨hF, hG, hmem⟩⟩

end DomainTheory.Neighborhood
