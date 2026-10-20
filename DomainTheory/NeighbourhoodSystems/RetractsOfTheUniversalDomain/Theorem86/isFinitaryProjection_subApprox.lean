module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.isProjection_subApprox

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6


















/-- **Theorem 8.6(b), in full.** `subApprox` is a finitary projection on `(E → E)`. -/
theorem isFinitaryProjection_subApprox : IsFinitaryProjection (subApprox (E := E)) :=
  ⟨isProjection_subApprox, isFinitary_subApprox⟩

end Sub8_6
end DomainTheory.NeighbourhoodSystems
