module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.continuous_subFilter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`sub`, packaged as a genuine approximable map on the function space `(E → E)`** (Scott's
remark that `f ↦ sub(f)` is itself approximable), via Exercise 2.13's `ofContinuous`. -/
def subApprox : ApproximableMap (funSpace E E) (funSpace E E) :=
  ofContinuous subFilter continuous_subFilter

end Sub8_6

end DomainTheory.NeighbourhoodSystems
