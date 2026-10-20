module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.isRetraction_subApprox
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subApprox_le_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6















/-- **`sub` is itself a *projection* on the function space `(E → E)`** (half of Theorem 8.6's
second clause; the other half, `IsFinitary subApprox`, is below). -/
theorem isProjection_subApprox : IsProjection (subApprox (E := E)) :=
  ⟨isRetraction_subApprox, subApprox_le_idMap⟩

end Sub8_6
end DomainTheory.NeighbourhoodSystems
