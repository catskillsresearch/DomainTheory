/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic
import DomainTheory.DataTypesAsLattices.Classification.theorem_6_3


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































/-- **Scott 1976, Table 3 / Theorem 6.3.** `𝔊_δ` is the class of continuous
preimages of `{⊤}`. -/
theorem typicalGdelta_universal (U : Set Pomega) :
    IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalGdelta} :=
  theorem_6_3 U

end DomainTheory.DataTypesAsLattices
