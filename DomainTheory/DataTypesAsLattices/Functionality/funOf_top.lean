/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices



theorem funOf_top (x : Pomega) : funOf topElem x = topElem := by
  ext m
  constructor
  · intro
    trivial
  · intro
    exact ⟨0, by simp [e_zero], trivial⟩

end DomainTheory.DataTypesAsLattices
