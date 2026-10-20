/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.Exercise713.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise713

open NeighborhoodSystem Domain.Recursive




variable {α : Type*} {V : NeighborhoodSystem α}







/-- **Round-trip A.** Starting from an abstract `InclStructure I`, building the hint system and its
presentation, then reading off the integer inclusion relation recovers `I.INCL` exactly. -/
theorem ofPresentation_toPresentation_INCL (I : InclStructure) (n m : ℕ) :
    (ofPresentation I.toPresentation).INCL n m ↔ I.INCL n m := by
  show I.toNbhd n ⊆ I.toNbhd m ↔ I.INCL n m
  exact I.toNbhd_subset_iff

end DomainTheory.Neighborhood.Exercise713
