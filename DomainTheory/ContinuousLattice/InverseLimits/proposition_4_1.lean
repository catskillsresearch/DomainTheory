/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Theorem212
import Mathlib.Order.GaloisConnection.Basic
import DomainTheory.ContinuousLattice.InverseLimits.Basic
import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_t0Space
import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_specializationLe_iff
import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_isInjectiveSpace


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))



















/-- **Scott 1972, Proposition 4.1.** The inverse limit is injective by the coordinatewise
Proposition 3.8/Lemma 3.9 construction; Theorem 2.12 then gives the continuous-lattice structure
on the existing componentwise complete lattice. -/
theorem proposition_4_1 (hD : ∀ n, IsContinuousLattice (D n)) :
    IsContinuousLattice (InverseLimit D P) := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := inverseLimit_t0Space D P
  exact (theorem_2_12_backward_exact (inverseLimit_isInjectiveSpace D P hD)
    (inverseLimit_specializationLe_iff D P)).1

end InverseLimit
end DomainTheory.ContinuousLattice
