/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Theorem212
import Mathlib.Order.GaloisConnection.Basic
import DomainTheory.ContinuousLattice.InverseLimits.Basic
import DomainTheory.ContinuousLattice.InverseLimits.embInf_family_directed


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
















































/-- **Scott 1972, §4.** Each `x ∈ D_∞` is the (monotone) lub of its projections:
`x = ⨆ₙ i_{n∞}(xₙ)`. -/
theorem inverseLimit_eq_iSup (x : InverseLimit D P) :
    x = ⨆ n, embInf D P n (x.1 n) := by
  have hdir := embInf_family_directed D P x
  have hne : (Set.range (fun n => embInf D P n (x.1 n))).Nonempty := Set.range_nonempty _
  refine le_antisymm ?_ ?_
  · rw [← Subtype.coe_le_coe]
    have hcoe : ((⨆ n, embInf D P n (x.1 n) : InverseLimit D P)).1
        = sSup (Subtype.val '' Set.range (fun n => embInf D P n (x.1 n))) := by
      rw [← sSup_range]
      exact coe_sSup_of_directed D P _ hne hdir
    rw [hcoe]
    intro m
    have hmem : (embInf D P m (x.1 m)).1
        ∈ Subtype.val '' Set.range (fun n => embInf D P n (x.1 n)) :=
      ⟨embInf D P m (x.1 m), ⟨m, rfl⟩, rfl⟩
    have hle := (le_sSup hmem) m
    rwa [show (embInf D P m (x.1 m)).1 m = x.1 m from iComp_self D P m (x.1 m)] at hle
  · exact iSup_le fun n => by
      rw [← Subtype.coe_le_coe]; intro m; exact iComp_incl_le D P n x m

end InverseLimit
end DomainTheory.ContinuousLattice
