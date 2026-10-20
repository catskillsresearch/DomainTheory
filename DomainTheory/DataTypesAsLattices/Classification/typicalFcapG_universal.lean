/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic
import DomainTheory.DataTypesAsLattices.Classification.theorem_6_4


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































/-- **Scott 1976, Table 3 / Theorem 6.4.** `𝔉 ∩̇ 𝔊` is the class of continuous
preimages of `{0}`. -/
theorem typicalFcapG_universal (U : Set Pomega) :
    IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalFcapG} :=
  theorem_6_4 U

end DomainTheory.DataTypesAsLattices
