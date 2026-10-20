/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.filterEnv

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem filterEnv_combinatory : ∀ i, IsCombinatory (filterEnv i)
  | 3 => filterRealizer_combinatory
  | 4 => pairComb_combinatory
  | 5 => dollarC_combinatory
  | 6 => .pred
  | 7 => topElem_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 8 => botElem_combinatory

end DomainTheory.DataTypesAsLattices
