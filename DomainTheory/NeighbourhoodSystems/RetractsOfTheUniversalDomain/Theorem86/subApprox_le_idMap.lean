module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6















/-- **`subApprox` is a projection**: `subApprox ≤ idMap`, from `subFilter φ ≤ φ`, itself
inherited from `sub_le`. -/
theorem subApprox_le_idMap : subApprox ≤ idMap (funSpace E E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_subApprox, toElementMap_idMap]
  calc subFilter φ = toFilter (sub (toApproxMap φ)) := rfl
    _ ≤ toFilter (toApproxMap φ) := toFilter_le_iff.mpr (sub_le _)
    _ = φ := toFilter_toApproxMap φ

end Sub8_6
end DomainTheory.NeighbourhoodSystems
