module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_ne
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem component_ofSeq (seq : ℕ → V.Element) (n : ℕ) :
    component (ofSeq seq) n = seq n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨_, _, hfib⟩
    have := hfib n; rwa [fiber_single_self] at this
  · intro hX
    refine ⟨(seq n).sub hX, single_mem ((seq n).sub hX), fun i => ?_⟩
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact (seq i).master_mem

end DomainTheory.NeighbourhoodSystems
