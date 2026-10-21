/-ai
Each bit neighbourhood belongs to the truth system.

Case on the bit: the zero neighbourhood and the one neighbourhood are neighbourhoods of the truth system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem bitNbhd_mem (b : Bool) : T.mem (bitNbhd b) := by
  cases b
  · exact Example12.mem_zero
  · exact Example12.mem_one

end DomainTheory.NeighbourhoodSystems.Exercise317
