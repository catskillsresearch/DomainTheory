/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_eq_diff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.U_diff_iff_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`\`, for `𝒰`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable — mirrors
`U_cons_computable` exactly, substituting `Udiff` for the raw `combineCode` composite. -/
theorem U_diff_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n \ UX m) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp Udiff_primrec)
  show (∃ k, UX k = UX t.unpair.1 \ UX t.unpair.2) ↔ _
  rw [U_diff_iff_nonempty, ← Udiff_eq_diff]

end DomainTheory.NeighbourhoodSystems
