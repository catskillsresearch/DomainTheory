/-ai
If a string has bit b at an index, the fiber of its encoding at that index is the bit neighbourhood of b.

By extensionality, a token in the fiber meets the encoding condition for b. Conversely, a token in that bit neighbourhood meets every bit constraint at the index, because the only defined bit there is b.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem fiber_encSet_some {σ : Str} {i : ℕ} {b : Bool} (h : σ[i]? = some b) :
    fiber (encSet σ) i = bitNbhd b := by
  ext t
  simp only [mem_fiber, mem_encSet]
  constructor
  · intro hh; exact hh b h
  · intro ht b' hb'; rw [h] at hb'; cases hb'; exact ht

end DomainTheory.NeighbourhoodSystems.Exercise317
