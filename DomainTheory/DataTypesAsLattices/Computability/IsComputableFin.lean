/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.IsRE

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- **Scott 1976, §2, Definition.** A `k`-ary continuous map is computable
when its nested graph (the pairing encoding of
`m ∈ f(e n₀)⋯(e n_{k-1})`) is r.e. -/
def IsComputableFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop :=
  IsScottContinuousFin f ∧ IsRE (curryFin f)

end DomainTheory.DataTypesAsLattices
