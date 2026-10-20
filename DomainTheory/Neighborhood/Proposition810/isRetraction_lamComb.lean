/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition89
public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.Proposition810.Basic
public import DomainTheory.Neighborhood.Proposition810.toApproxMap_toElementMap_lamComb

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **Proposition 8.10, `→`-case (the `lamComb` half), retraction.** -/
theorem isRetraction_lamComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (lamComb a b) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_lamComb a b ((lamComb a b).toElementMap φ),
    toApproxMap_toElementMap_lamComb a b φ,
    comp_assoc b ((toApproxMap φ).comp a) a,
    ← comp_assoc b b (((toApproxMap φ).comp a).comp a), hb,
    comp_assoc (toApproxMap φ) a a, ha]

end DomainTheory.Neighborhood
