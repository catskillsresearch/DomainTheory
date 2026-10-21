/-ai
The packaged map subApprox is a retraction: its composite with itself equals itself.

Antisymmetry gives the two inequalities. Each is the elementwise characterization of the order, and at every element the element map of the composite equals the element map of subApprox, so each direction of that equality is one inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toElementMap_subApprox_comp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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
end DomainTheory.NeighbourhoodSystems
