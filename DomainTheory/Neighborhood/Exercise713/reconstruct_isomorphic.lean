/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Exercise713.Basic


namespace DomainTheory.Neighborhood.Exercise713

open NeighborhoodSystem Domain.Recursive




variable {α : Type*} {V : NeighborhoodSystem α}












/-- **Exercise 7.13 (⇒, "essentially any effectively given system").** The system reconstructed from
an effectively given `V` via its `INCL` relation is domain-isomorphic to `V`. -/
theorem reconstruct_isomorphic (P : ComputablePresentation V) : reconstruct P ≅ᴰ V :=
  ⟨(reconIso P).symm⟩

end DomainTheory.Neighborhood.Exercise713
