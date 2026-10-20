/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88b.Basic
public import DomainTheory.Neighborhood.Theorem88b.eIdx_zero
public import DomainTheory.Neighborhood.Theorem88b.he0
public import DomainTheory.Neighborhood.Theorem88b.hcover
public import DomainTheory.Neighborhood.Theorem88b.genAtom_empty_iff
public import DomainTheory.Neighborhood.Theorem88c.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)



















/-- **Theorem 8.8(b), Part 6.** If `D` is effectively given, then Theorem 8.8(a)'s own subsystem
`D'` (with `D ≅ᴰ D'` and `D' ◁ U`, from `isomorphic_DprimeU`/`DprimeU_subsystem`) is *also*
effectively given. -/
theorem DprimeU_isEffectivelyGiven :
    (DprimeU D (e P) (hcover P) (he0 P)).IsEffectivelyGiven :=
  ⟨DprimeUPresentation P⟩

end DomainTheory.Neighborhood
