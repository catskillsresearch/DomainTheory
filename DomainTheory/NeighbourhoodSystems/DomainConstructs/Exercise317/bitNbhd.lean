module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The `T`-neighbourhood selected by a bit: `false ↦ {0}`, `true ↦ {1}`. -/
def bitNbhd : Bool → Set Token
  | false => Example12.zero
  | true => Example12.one

end DomainTheory.NeighbourhoodSystems.Exercise317
