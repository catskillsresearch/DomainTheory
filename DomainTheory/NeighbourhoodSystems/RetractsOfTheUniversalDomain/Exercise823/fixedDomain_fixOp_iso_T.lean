/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem86
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise816
public import DomainTheory.Neighborhood.Exercise823.Basic
public import DomainTheory.Neighborhood.Exercise823.isFinitaryProjection_fixOp
public import DomainTheory.Neighborhood.Exercise823.tOp_fixOp

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}











/-- **Exercise 8.23, Claim 2 (the domain equation).** Given any correspondence `T` (bundling, for
each map, a type and a domain over it) with `Fix(t(a)) ≅ T(a)` for every finitary projection `a`
(Scott's hypothesis `D_{t(a)} ≅ T(D_a)`), substituting the *exact* fixed point `a := ‖t‖` and using
`tOp_fixOp` gives `Fix(‖t‖) ≅ T(‖t‖)` unconditionally — no colimit/continuity argument needed,
since `‖t‖` solves the equation on the nose rather than merely in the limit. -/
theorem fixedDomain_fixOp_iso_T (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, IsFinitaryProjection a → IsFinitaryProjection (tOp t a))
    (T : ApproximableMap E E → Σ β : Type, NeighborhoodSystem β)
    (hT : ∀ a, IsFinitaryProjection a → Nonempty (Fix (tOp t a) ≃o (T a).2.Element)) :
    Nonempty (Fix (fixOp t) ≃o (T (fixOp t)).2.Element) := by
  have h := hT (fixOp t) (isFinitaryProjection_fixOp t ht)
  rwa [tOp_fixOp] at h

end Exercise823
end DomainTheory.Neighborhood
