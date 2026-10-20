/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.Example78.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Example78

open Domain.Recursive NeighborhoodSystem







/-- **Any two neighbourhoods of `PN` are consistent** (Scott: "any two neighbourhoods are
consistent"): their intersection `nbhd (n ||| m)` is itself a neighbourhood contained in both. -/
theorem PN_consistent (n m : ℕ) : ∃ k, nbhd k ⊆ nbhd n ∩ nbhd m :=
  ⟨myLor n m, (nbhd_inter n m).symm.subset⟩

end DomainTheory.Neighborhood.Example78
