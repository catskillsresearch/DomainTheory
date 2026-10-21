/-ai
For each bit there is a truth token outside its bit neighbourhood.

For false, the token 1 lies outside the zero neighbourhood. For true, the token 0 lies outside the one neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap




theorem exists_not_mem_bitNbhd (b : Bool) : ∃ t : Token, t ∉ bitNbhd b := by
  cases b
  · exact ⟨1, by simp [bitNbhd, Example12.zero]⟩
  · exact ⟨0, by simp [bitNbhd, Example12.one]⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
