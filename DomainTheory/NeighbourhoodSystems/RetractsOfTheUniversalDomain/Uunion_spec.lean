/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_eq_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_UX_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Uunion n m` genuinely indexes `UX n ∪ UX m`** — mirrors `Udiff_spec`'s shape exactly, but the
hypothesis is never used (the union is already unconditionally genuine, `U_union_mem`): the raw
`appendListCode` output is already a genuine `U`-neighbourhood, so re-canonicalizing it (`canonCode`'s
own lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem Uunion_spec {n m : ℕ} (_ : ∃ k, UX k = UX n ∪ UX m) : UX (Uunion n m) = UX n ∪ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Uunion n m))) := by
    rw [Uunion_eq_union]; exact U_union_UX_mem n m
  show presentedIntervals (decodeQPairList (canonCode (Uunion n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Uunion_eq_union]

end DomainTheory.NeighbourhoodSystems
