module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem ofSeq_mono {seq seq' : ℕ → V.Element} (h : ∀ n, seq n ≤ seq' n) :
    ofSeq seq ≤ ofSeq seq' := by
  rintro W ⟨hW, hf⟩
  exact ⟨hW, fun i => h i _ (hf i)⟩

end DomainTheory.NeighbourhoodSystems
