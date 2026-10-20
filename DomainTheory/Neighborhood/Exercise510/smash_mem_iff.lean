/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise510.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise510

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}



variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





theorem smash_mem_iff {W : Set (α ⊕ β)} :
    (smash V₀ V₁).mem W ↔
      W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W := Iff.rfl

end DomainTheory.Neighborhood.Exercise510
