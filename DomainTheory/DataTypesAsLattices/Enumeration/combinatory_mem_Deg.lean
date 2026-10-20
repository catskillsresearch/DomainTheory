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
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





















































/-- Combinatory elements lie in every enumeration degree, since `Deg a`
contains `G` and is closed under application. -/
theorem combinatory_mem_Deg (a : Pomega) {u : Pomega}
    (hu : IsCombinatory u) : u ∈ Deg a := by
  have huG : GeneratedFromG u := (theorem_3_1 (u := u)).mp hu
  clear hu
  induction huG with
  | G => exact (Deg_isSubalgebra a).1
  | app _ _ ih ih' => exact (Deg_isSubalgebra a).2 ih ih'

end DomainTheory.DataTypesAsLattices
