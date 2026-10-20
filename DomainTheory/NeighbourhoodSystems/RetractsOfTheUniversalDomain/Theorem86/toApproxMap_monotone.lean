module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_monotone {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) :
    toApproxMap φ ≤ toApproxMap ψ := by
  have := (funSpaceEquiv E E).monotone h
  simpa using this

end Sub8_6

end DomainTheory.NeighbourhoodSystems
