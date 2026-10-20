/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.DAtomDecidable
public import DomainTheory.Neighborhood.SplitU
public import DomainTheory.Neighborhood.UComputablePresentation
public import DomainTheory.Neighborhood.Theorem88b.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem eIdx_zero : eIdx P 0 = P.masterIdx := ite_eq_left rfl

end DomainTheory.Neighborhood
