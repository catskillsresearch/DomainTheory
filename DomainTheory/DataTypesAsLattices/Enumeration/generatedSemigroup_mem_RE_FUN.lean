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
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_mem_FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_mem_FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar_mem_FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp_mem_FUN

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





















































theorem generatedSemigroup_mem_RE_FUN {u : Pomega} (hu : GeneratedSemigroup u) :
    u ∈ RE ∩ FUN := by
  induction hu with
  | R => exact ⟨Rcomb_combinatory, Rcomb_mem_FUN⟩
  | L => exact ⟨Lcomb_combinatory, Lcomb_mem_FUN⟩
  | Gbar => exact ⟨Gbar_combinatory, Gbar_mem_FUN⟩
  | comp _ _ ihu ihv =>
      exact ⟨enumComp_combinatory ihu.1 ihv.1, enumComp_mem_FUN _ _⟩

end DomainTheory.DataTypesAsLattices
