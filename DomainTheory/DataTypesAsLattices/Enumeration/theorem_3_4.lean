/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4_diagonal
import DomainTheory.DataTypesAsLattices.Enumeration.primrec_diagonalInterCode
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_diagonalInterCode


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices
























































/-- **Scott 1976, Theorem 3.4 (The incompleteness theorem).**
The set of Gödel numbers denoting bottom is not recursively enumerable. -/
theorem theorem_3_4 :
    ¬ IsRE {n | valNat n = botElem} := by
  intro hb
  have hpre : IsRE {i | diagonalInterCode i ∈ {n | valNat n = botElem}} :=
    hb.comp primrec_diagonalInterCode.to_comp
  obtain ⟨k, hk⟩ :=
    theorem_3_2_surjective (IsRE.combinatory hpre)
  exact theorem_3_4_diagonal (val := valNat) (v := diagonalInterCode)
    valNat_diagonalInterCode rfl ⟨k, hk⟩


end DomainTheory.DataTypesAsLattices
