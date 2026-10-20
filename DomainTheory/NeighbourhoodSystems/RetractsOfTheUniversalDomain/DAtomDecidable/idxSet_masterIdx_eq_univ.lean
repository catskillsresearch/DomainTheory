/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88a.Basic
public import DomainTheory.Neighborhood.Theorem88a.idxSet_nonempty
public import DomainTheory.Neighborhood.Theorem88a.idxSet_eq_iff
public import DomainTheory.Neighborhood.Theorem88a.isomorphic_DprimeU
public import DomainTheory.Neighborhood.Theorem88a.theorem_8_8_a
public import DomainTheory.Neighborhood.Theorem88a.theorem_8_8
public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.DAtomDecidable.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)





/-- `idxSet P.X P.masterIdx = Set.univ`: `masterIdx` indexes `D`'s master `Δ`, and every
`D`-neighbourhood is `⊆ Δ`. -/
theorem idxSet_masterIdx_eq_univ : idxSet P.X P.masterIdx = Set.univ :=
  Set.eq_univ_of_forall fun m => by
    show P.X m ⊆ P.X P.masterIdx
    rw [P.masterIdx_spec]
    exact D.sub_master (P.mem_X m)

end DomainTheory.Neighborhood
