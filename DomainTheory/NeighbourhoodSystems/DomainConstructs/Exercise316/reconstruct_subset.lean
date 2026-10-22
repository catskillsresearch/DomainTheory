module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.interUpTo_subset_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- The finite intersection `⋂_{i<N} single i (fiber W i)` reconstructs `W` from below, once `N`
exceeds the cofinite-`Δ` bound of `W`. -/
theorem reconstruct_subset {W : Set (ℕ × α)} (_hW : (iterSys V).mem W) {N : ℕ}
    (hN : ∀ i, N ≤ i → fiber W i = V.master) :
    (iterSys V).interUpTo (fun i => single V i (fiber W i)) N ⊆ W := by
  rintro ⟨j, a⟩ ha
  by_cases h : j < N
  · have hsub := (iterSys V).interUpTo_subset (fun i => single V i (fiber W i)) h
    have hmem : (j, a) ∈ single V j (fiber W j) := hsub ha
    simpa [single] using hmem
  · have haM : a ∈ V.master := interUpTo_subset_master (fun i => single V i (fiber W i)) N ha
    have : a ∈ fiber W j := by rw [hN j (not_lt.mp h)]; exact haM
    exact this

end DomainTheory.NeighbourhoodSystems
