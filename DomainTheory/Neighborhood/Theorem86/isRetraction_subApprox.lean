/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem85
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise213
public import DomainTheory.Neighborhood.Proposition611
public import DomainTheory.Neighborhood.Theorem86.Basic
public import DomainTheory.Neighborhood.Theorem86.toElementMap_subApprox_comp

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6















/-- **`subApprox` is a retraction**: `subApprox ∘ subApprox = subApprox`, from `subFilter`'s own
idempotency (`subFilter_subFilter`), itself inherited from `sub_sub`. Proved via `le_antisymm` on
`le_iff_toElementMap_le` (choice-free), rather than the classical `ext_of_toElementMap`. -/
theorem isRetraction_subApprox : IsRetraction (subApprox (E := E)) :=
  le_antisymm (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).le)
    (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).ge)

end Sub8_6
end DomainTheory.Neighborhood
