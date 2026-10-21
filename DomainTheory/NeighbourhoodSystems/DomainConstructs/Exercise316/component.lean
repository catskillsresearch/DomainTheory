/-ai
The n-th component of an iterate element is the original element whose neighbourhoods are the sets X such that X is a neighbourhood and the iterate element contains the pinning of copy n to X. The subfamily law is the first conjunct. The master belongs because pinning the master yields the iterate master. An intersection of two such pinnings is the pinning of the intersection, and that intersection is a neighbourhood because its fiber at the pinned copy belongs to the iterate element. Upward closure uses monotonicity of pinning.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The `n`-th component `xₙ ∈ |𝒟|` of a `𝒟^∞`-element `z` (Scott's coordinate at copy `n`). -/
def component (z : (iterSys V).Element) (n : ℕ) : V.Element where
  mem X := V.mem X ∧ z.mem (single V n X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [single_master]; exact z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz : z.mem (single V n (X ∩ X')) := by rw [← single_inter]; exact z.inter_mem hzX hzX'
    have hmem : V.mem (X ∩ X') := by
      have := (z.sub hz).1 n; rwa [fiber_single_self] at this
    exact ⟨hmem, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    exact ⟨hX', z.up_mem hzX (single_mem hX') (single_mono hXX')⟩

end DomainTheory.NeighbourhoodSystems
