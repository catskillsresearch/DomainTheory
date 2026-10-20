/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unionBits_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.e_eq_unionBits

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


























































theorem e_combinatory (j : ℕ) : IsCombinatory (e j) := by
  simpa [e_eq_unionBits] using unionBits_combinatory (bitList j)

end DomainTheory.DataTypesAsLattices
