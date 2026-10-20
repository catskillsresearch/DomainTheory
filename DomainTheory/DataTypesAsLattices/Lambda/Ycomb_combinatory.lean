/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_closed
public import DomainTheory.DataTypesAsLattices.Lambda.Yterm_interp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















































theorem Ycomb_combinatory : IsCombinatory Ycomb := by
  simpa [Yterm_interp] using theorem_2_4_closed Yterm

end DomainTheory.DataTypesAsLattices
