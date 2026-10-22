module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.subset_single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.reconstruct_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component_ofSeq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem ofSeq_component (z : (iterSys V).Element) :
    ofSeq (fun n => component z n) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hW, hfib⟩
    obtain ⟨N, hN⟩ := hW.2
    exact z.up_mem (z.mem_interUpTo _ (n := N) (fun i _ => (hfib i).2)) hW
      (reconstruct_subset hW hN)
  · intro hzW
    refine ⟨z.sub hzW, fun i => ?_⟩
    exact ⟨(z.sub hzW).1 i, z.up_mem hzW (single_mem ((z.sub hzW).1 i)) (subset_single (z.sub hzW) i)⟩

end DomainTheory.NeighbourhoodSystems
