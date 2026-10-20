/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88a
public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.DAtomDecidable.Basic
public import DomainTheory.Neighborhood.DAtomDecidable.mem_IPos

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)





theorem mem_DAtom {pos neg : List ℕ} {m : ℕ} :
    m ∈ DAtom P pos neg ↔ (∀ i ∈ pos, P.X m ⊆ P.X i) ∧ (∀ j ∈ neg, ¬ P.X m ⊆ P.X j) := by
  simp only [DAtom, Set.mem_inter_iff, mem_IPos, Set.mem_ofPred_eq, mem_idxSet]

end DomainTheory.Neighborhood
