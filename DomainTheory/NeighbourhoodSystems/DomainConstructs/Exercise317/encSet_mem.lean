/-ai
The encoding of any binary string is a neighbourhood of the infinite iterate of the truth system.

At an index where the string is undefined, the fiber is the universal set, hence the master; where the string has a bit, the fiber is that bit neighbourhood. From the length of the string onward the string is undefined, so every such fiber equals the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fiber_encSet_some
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fiber_encSet_none
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `encSet σ` is a `T^∞`-neighbourhood. -/
theorem encSet_mem (σ : Str) : (iterSys T).mem (encSet σ) := by
  refine ⟨fun i => ?_, σ.length, fun i hi => ?_⟩
  · cases h : σ[i]? with
    | none => rw [fiber_encSet_none h]; exact T.master_mem
    | some b => rw [fiber_encSet_some h]; exact bitNbhd_mem b
  · rw [fiber_encSet_none (List.getElem?_eq_none_iff.mpr hi)]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise317
