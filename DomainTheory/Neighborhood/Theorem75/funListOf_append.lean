/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
































theorem funListOf_append (la lb : List ℕ) :
    funListOf P₀ P₁ (la ++ lb) = funListOf P₀ P₁ la ++ funListOf P₀ P₁ lb := by
  simp [funListOf, List.map_append]

end DomainTheory.Neighborhood
