/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Theorem212
import Mathlib.Order.GaloisConnection.Basic
import DomainTheory.ContinuousLattice.InverseLimits.Basic
import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_eq_iSup


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
















































/-- **Scott 1972, §4 (functional equation, "the remark following 4.2").** The identity of `D_∞` is
the directed lub of the approximating projections `rₙ = i_{n∞} ∘ j_{∞n}`:
`id = ⨆ₙ i_{n∞} ∘ j_{∞n}`. This is the algebraic identity at the heart of Theorem 4.4. -/
theorem idInf_eq_iSup :
    (ScottMap.idMap : ScottMap (InverseLimit D P) (InverseLimit D P))
      = ⨆ n, (embInf D P n).comp (projInf D P n) := by
  apply ScottMap.ext
  intro x
  rw [show (⨆ n, (embInf D P n).comp (projInf D P n))
        = sSup (Set.range fun n => (embInf D P n).comp (projInf D P n)) from sSup_range.symm,
    ScottMap.sSup_apply, ScottMap.idMap_apply, ← Set.range_comp, sSup_range]
  exact inverseLimit_eq_iSup D P x

end InverseLimit
end DomainTheory.ContinuousLattice
