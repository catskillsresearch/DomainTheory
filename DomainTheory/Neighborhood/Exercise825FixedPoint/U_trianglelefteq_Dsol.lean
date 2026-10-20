/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise823
import DomainTheory.Neighborhood.Exercise715
import DomainTheory.Neighborhood.Exercise825Pow
import DomainTheory.Neighborhood.Exercise825Embed
import DomainTheory.Neighborhood.Exercise825Closing
import DomainTheory.Neighborhood.Exercise820
import DomainTheory.Neighborhood.Exercise825FixedPoint.Basic
import DomainTheory.Neighborhood.Exercise825FixedPoint.fixedNbhd_cCombinator_isomorphic
import DomainTheory.Neighborhood.Exercise825FixedPoint.Dsol_isomorphic_funSpace_cCombinator


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap




















/-- **`𝒰 ⊴ D`**: the solution domain contains a copy of the universal domain `𝒰`, so it is
non-trivial (Scott's remark). Chains `𝒰 ⊴ 𝒰^∞` (`Exercise825Embed.trianglelefteq_iterSys`),
`𝒰^∞ ≅ fixedNbhd c`, the general constant-function embedding `𝒱 ⊴ (𝒟 → 𝒱)`
(`Exercise820.trianglelefteq_funSpace_const`), and `D → (fixedNbhd c) ≅ D`. -/
theorem U_trianglelefteq_Dsol : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) := by
  set D := fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) with hD
  have h1 : U ⊴ iterSys U := trianglelefteq_iterSys U
  have h2 : iterSys U ⊴ fixedNbhd cCombinator :=
    ⟨fixedNbhd cCombinator, Subsystem.refl _, fixedNbhd_cCombinator_isomorphic.symm⟩
  have h3 : fixedNbhd cCombinator ⊴ funSpace D (fixedNbhd cCombinator) :=
    trianglelefteq_funSpace_const D (fixedNbhd cCombinator)
  have h4 : funSpace D (fixedNbhd cCombinator) ⊴ D :=
    ⟨D, Subsystem.refl D, Dsol_isomorphic_funSpace_cCombinator.symm⟩
  exact trianglelefteq_trans (trianglelefteq_trans (trianglelefteq_trans h1 h2) h3) h4

end DomainTheory.Neighborhood
